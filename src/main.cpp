#include "sat_solver.hpp"

#include <SFML/Graphics.hpp>
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <sstream>

namespace {

const sf::Color background(14, 20, 29);
const sf::Color panel(24, 33, 45);
const sf::Color panelLight(31, 43, 58);
const sf::Color ink(235, 241, 247);
const sf::Color muted(157, 171, 187);
const sf::Color cyan(66, 211, 190);
const sf::Color orange(255, 176, 92);
const sf::Color red(247, 108, 108);

struct Fonts {
    sf::Font primary;
    sf::Font fallback;
    sf::Font symbols;
};

struct UnicodeRun {
    std::u32string value;
    const sf::Font* font = nullptr;
};

std::u32string utf8ToUtf32(const std::string& value) {
    std::u32string result;
    for (size_t i = 0; i < value.size();) {
        const auto first = static_cast<unsigned char>(value[i++]);
        char32_t codepoint = 0;
        size_t continuation = 0;
        if (first < 0x80) codepoint = first;
        else if ((first & 0xE0) == 0xC0) { codepoint = first & 0x1F; continuation = 1; }
        else if ((first & 0xF0) == 0xE0) { codepoint = first & 0x0F; continuation = 2; }
        else if ((first & 0xF8) == 0xF0) { codepoint = first & 0x07; continuation = 3; }
        else { result.push_back(0xFFFD); continue; }
        if (i + continuation > value.size()) { result.push_back(0xFFFD); break; }
        bool valid = true;
        for (size_t j = 0; j < continuation; ++j) {
            const auto part = static_cast<unsigned char>(value[i++]);
            if ((part & 0xC0) != 0x80) { valid = false; break; }
            codepoint = (codepoint << 6) | (part & 0x3F);
        }
        result.push_back(valid ? codepoint : 0xFFFD);
    }
    return result;
}

std::vector<UnicodeRun> splitRuns(const Fonts& fonts, const std::string& value) {
    std::vector<UnicodeRun> runs;
    for (char32_t codepoint : utf8ToUtf32(value)) {
        const sf::Font* selected = fonts.primary.hasGlyph(codepoint) ? &fonts.primary :
            (fonts.fallback.hasGlyph(codepoint) ? &fonts.fallback :
            (fonts.symbols.hasGlyph(codepoint) ? &fonts.symbols : nullptr));
        if (selected == nullptr) selected = &fonts.primary;
        if (runs.empty() || runs.back().font != selected) runs.push_back({{}, selected});
        runs.back().value.push_back(codepoint);
    }
    return runs;
}

void rectangle(sf::RenderWindow& window, sf::Vector2f position, sf::Vector2f size, sf::Color color, float radius = 0.f) {
    sf::RectangleShape shape(size);
    shape.setPosition(position);
    shape.setFillColor(color);
    window.draw(shape);
}

float textWidth(const Fonts& fonts, const std::string& value, unsigned size) {
    float width = 0.f;
    for (const auto& run : splitRuns(fonts, value)) {
        sf::Text drawable(*run.font, sf::String(run.value), size);
        width += drawable.getLocalBounds().size.x;
    }
    return width;
}

void text(sf::RenderWindow& window, const Fonts& fonts, const std::string& value, sf::Vector2f position,
          unsigned size, sf::Color color = ink) {
    for (const auto& run : splitRuns(fonts, value)) {
        sf::Text drawable(*run.font, sf::String(run.value), size);
        drawable.setPosition(position);
        drawable.setFillColor(color);
        window.draw(drawable);
        position.x += drawable.getLocalBounds().size.x;
    }
}

std::vector<std::string> lines(const std::string& value) {
    std::vector<std::string> result;
    std::stringstream stream(value);
    std::string line;
    while (std::getline(stream, line)) result.push_back(line);
    if (result.empty()) result.push_back("");
    return result;
}

void drawWrapped(sf::RenderWindow& window, const Fonts& fonts, const std::string& value, sf::Vector2f position,
                 float width, unsigned size, sf::Color color = ink, float lineHeight = 1.35f) {
    for (const auto& sourceLine : lines(value)) {
        std::string current;
        std::stringstream words(sourceLine);
        std::string word;
        while (words >> word) {
            const std::string candidate = current.empty() ? word : current + " " + word;
            if (!current.empty() && textWidth(fonts, candidate, size) > width) {
                text(window, fonts, current, position, size, color);
                position.y += static_cast<float>(size) * lineHeight;
                current = word;
            } else current = candidate;
        }
        text(window, fonts, current, position, size, color);
        position.y += static_cast<float>(size) * lineHeight;
    }
}

std::vector<std::string> inputRules(const std::string& source) {
    std::vector<std::string> result;
    for (const auto& line : lines(source)) {
        if (!line.empty() && line.find_first_not_of(" \t\r") != std::string::npos) result.push_back(line);
    }
    return result;
}

void appendUtf8(std::string& target, char32_t codepoint) {
    if (codepoint < 0x80) target += static_cast<char>(codepoint);
    else if (codepoint < 0x800) {
        target += static_cast<char>(0xC0 | (codepoint >> 6));
        target += static_cast<char>(0x80 | (codepoint & 0x3F));
    } else if (codepoint < 0x10000) {
        target += static_cast<char>(0xE0 | (codepoint >> 12));
        target += static_cast<char>(0x80 | ((codepoint >> 6) & 0x3F));
        target += static_cast<char>(0x80 | (codepoint & 0x3F));
    }
}

void analyze(const std::string& source, sat::Analysis& analysis, std::string& status) {
    const auto rules = inputRules(source);
    if (rules.empty()) {
        analysis = {};
        status = "Escribe al menos una regla para comenzar.";
        return;
    }
    analysis = sat::solve(rules);
        status = analysis.error.empty() ? "Analisis completado" : "Error: " + analysis.error;
}

void drawAtoms(sf::RenderWindow& window, const Fonts& fonts, const sat::Analysis& analysis, sf::Vector2f origin) {
    text(window, fonts, "ATOMOS", origin, 16, cyan);
    float y = origin.y + 32.f;
    if (analysis.atoms.empty()) { text(window, fonts, "Aun no hay atomos", {origin.x, y}, 14, muted); return; }
    for (const auto& atom : analysis.atoms) {
        rectangle(window, {origin.x, y}, {34.f, 26.f}, cyan);
        text(window, fonts, std::string(1, analysis.letters.at(atom)), {origin.x + 11.f, y + 3.f}, 15, background);
        drawWrapped(window, fonts, atom, {origin.x + 46.f, y + 3.f}, 225.f, 14);
        y += 34.f;
    }
}

void drawRules(sf::RenderWindow& window, const Fonts& fonts, const sat::Analysis& analysis, sf::Vector2f origin) {
    text(window, fonts, "FORMULAS", origin, 16, cyan);
    float y = origin.y + 32.f;
    for (size_t i = 0; i < analysis.rules.size(); ++i) {
        text(window, fonts, "R" + std::to_string(i + 1), {origin.x, y}, 14, orange);
        drawWrapped(window, fonts, analysis.rules[i].text, {origin.x + 30.f, y}, 530.f, 13, muted);
        y += 28.f;
        text(window, fonts, sat::formulaText(analysis, analysis.rules[i].formula), {origin.x + 30.f, y}, 17);
        y += 34.f;
    }
}

void drawBranches(sf::RenderWindow& window, const Fonts& fonts, const sat::Analysis& analysis, sf::Vector2f origin) {
    text(window, fonts, "ARBOL SEMANTICO", origin, 16, cyan);
    float y = origin.y + 32.f;
    if (analysis.branches.empty()) { text(window, fonts, "Las ramas apareceran aqui", {origin.x, y}, 14, muted); return; }
    for (size_t i = 0; i < analysis.branches.size(); ++i) {
        const auto& branch = analysis.branches[i];
        const sf::Color state = branch.closed ? red : cyan;
        rectangle(window, {origin.x, y}, {690.f, 30.f}, branch.closed ? sf::Color(71, 37, 46) : sf::Color(27, 61, 61));
        text(window, fonts, "Rama " + std::to_string(i + 1), {origin.x + 12.f, y + 5.f}, 14, state);
        text(window, fonts, branch.closed ? "CERRADA  ×" : "ABIERTA  |  " + sat::branchModel(analysis, branch), {origin.x + 112.f, y + 5.f}, 14);
        y += 38.f;
        std::string formulas;
        for (int index : branch.formulas) {
            if (!formulas.empty()) formulas += "   ";
            formulas += sat::formulaText(analysis, index);
        }
        drawWrapped(window, fonts, formulas, {origin.x + 18.f, y}, 650.f, 14, muted);
        y += 28.f;
        for (const auto& step : branch.steps) {
            text(window, fonts, step.expanded ? "[aplicada]" : "[ ]", {origin.x + 30.f, y}, 12, orange);
            drawWrapped(window, fonts, step.expression + "  " + step.rule, {origin.x + 110.f, y}, 560.f, 12, muted);
            y += 22.f;
        }
        y += 8.f;
        if (y > 760.f) break;
    }
}

}

int main() {
    Fonts fonts;
    const bool primaryLoaded = fonts.primary.openFromFile("C:/Windows/Fonts/segoeui.ttf") ||
        fonts.primary.openFromFile("C:/Windows/Fonts/arial.ttf");
    const bool fallbackLoaded = fonts.fallback.openFromFile("C:/Windows/Fonts/swmath.ttf") ||
        fonts.fallback.openFromFile("C:/Windows/Fonts/cambriaz.ttf");
    const bool symbolsLoaded = fonts.symbols.openFromFile("C:/Windows/Fonts/seguisym.ttf") ||
        fonts.symbols.openFromFile("C:/Windows/Fonts/symbol.ttf") ||
        fonts.symbols.openFromFile("C:/Windows/Fonts/cambria.ttc");
    if (!primaryLoaded || !fallbackLoaded || !symbolsLoaded) {
        std::cerr << "No se pudieron cargar todas las fuentes Unicode.\n";
        return 1;
    }
    for (const char32_t glyph : {U'¬', U'∧', U'∨', U'→', U'↔', U'×', U'á', U'ñ'}) {
        if (!fonts.primary.hasGlyph(glyph) && !fonts.fallback.hasGlyph(glyph) && !fonts.symbols.hasGlyph(glyph)) {
            std::cerr << "Falta el glifo Unicode requerido: U+" << std::hex << static_cast<unsigned int>(glyph) << std::dec << '\n';
            return 1;
        }
    }
    sf::RenderWindow window(sf::VideoMode({1280, 820}), "SAT Solver | Tableau semantico");
    window.setFramerateLimit(60);
    std::string input;
    sat::Analysis analysis;
    std::string status = "Pulsa ANALIZAR para construir el tableau.";
    bool editing = true;
    float scroll = 0.f;
    while (window.isOpen()) {
        while (const std::optional event = window.pollEvent()) {
            if (event->is<sf::Event::Closed>()) window.close();
            if (const auto* key = event->getIf<sf::Event::KeyPressed>()) {
                if (key->code == sf::Keyboard::Key::Escape) window.close();
                if (key->code == sf::Keyboard::Key::Backspace && editing && !input.empty()) input.pop_back();
                if (key->code == sf::Keyboard::Key::Enter && editing) input += '\n';
            }
            if (const auto* entered = event->getIf<sf::Event::TextEntered>()) {
                if (editing && entered->unicode >= 32 && entered->unicode != 127) appendUtf8(input, entered->unicode);
            }
            if (const auto* mouse = event->getIf<sf::Event::MouseButtonPressed>()) {
                if (mouse->button == sf::Mouse::Button::Left) {
                    if (mouse->position.x >= 36 && mouse->position.x <= 206 && mouse->position.y >= 282 && mouse->position.y <= 326) {
                        analyze(input, analysis, status); editing = false;
                    }
                    if (mouse->position.x >= 220 && mouse->position.x <= 390 && mouse->position.y >= 282 && mouse->position.y <= 326) {
                        input.clear(); analysis = {}; status = "Escribe una o varias reglas."; editing = true;
                    }
                    if (mouse->position.x >= 36 && mouse->position.x <= 1170 && mouse->position.y >= 92 && mouse->position.y <= 265) editing = true;
                }
            }
            if (const auto* wheel = event->getIf<sf::Event::MouseWheelScrolled>()) scroll = std::clamp(scroll - wheel->delta * 35.f, 0.f, 800.f);
        }

        window.clear(background);
        text(window, fonts, "SAT-SOLVER", {36.f, 24.f}, 28, ink);
        text(window, fonts, "TABLEAU SEMANTICO", {220.f, 33.f}, 13, cyan);
        text(window, fonts, status, {760.f, 38.f}, 13, status.find("error") != std::string::npos ? red : muted);
        rectangle(window, {36.f, 82.f}, {1134.f, 184.f}, panel);
        text(window, fonts, "BASE DE CONOCIMIENTO", {52.f, 98.f}, 13, cyan);
        drawWrapped(window, fonts, input, {52.f, 124.f}, 1100.f, 16);
        rectangle(window, {36.f, 282.f}, {170.f, 44.f}, cyan);
        text(window, fonts, "ANALIZAR", {78.f, 294.f}, 15, background);
        rectangle(window, {220.f, 282.f}, {170.f, 44.f}, panelLight);
        text(window, fonts, "LIMPIAR", {268.f, 294.f}, 15, ink);
        text(window, fonts, "Una regla por linea. Enter crea otra regla.", {420.f, 296.f}, 13, muted);
        rectangle(window, {36.f, 350.f}, {1134.f, 1.f}, panelLight);
        drawAtoms(window, fonts, analysis, {36.f, 374.f});
        drawRules(window, fonts, analysis, {330.f, 374.f});
        drawBranches(window, fonts, analysis, {36.f, 570.f - scroll});
        size_t open = 0;
        for (const auto& branch : analysis.branches) if (!branch.closed) ++open;
        if (!analysis.branches.empty()) {
            rectangle(window, {870.f, 374.f}, {300.f, 116.f}, open ? sf::Color(27, 61, 61) : sf::Color(71, 37, 46));
            text(window, fonts, open ? "SATISFACIBLE" : "INCONSISTENTE", {894.f, 394.f}, 18, open ? cyan : red);
            text(window, fonts, std::to_string(open) + " rama(s) abierta(s)", {894.f, 432.f}, 14);
            text(window, fonts, "✕ = contradiccion", {894.f, 457.f}, 13, muted);
        }
        window.display();
    }
}