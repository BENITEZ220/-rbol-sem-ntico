#include "sat_solver.hpp"

#include <algorithm>
#include <cctype>
#include <set>
#include <sstream>

namespace sat {
namespace {

std::string trim(std::string text) {
    const auto first = text.find_first_not_of(" \t\r\n");
    const auto last = text.find_last_not_of(" \t\r\n");
    return first == std::string::npos ? "" : text.substr(first, last - first + 1);
}

std::string normalize(std::string text) {
    text = trim(text);
    // Lowercase ASCII bytes only; this preserves UTF-8 accents and ñ.
    for (char& c : text) {
        if (c >= 'A' && c <= 'Z') c = static_cast<char>(c - 'A' + 'a');
    }
    while (!text.empty() && (text.back() == '.' || text.back() == ';' || text.back() == '!' || text.back() == '?')) text.pop_back();
    std::string compact;
    bool space = false;
    for (char c : trim(text)) {
        if (std::isspace(static_cast<unsigned char>(c))) space = true;
        else {
            if (space && !compact.empty()) compact += ' ';
            compact += c;
            space = false;
        }
    }
    return compact;
}

struct Parser {
    Analysis& result;
    std::vector<std::string> tokens;
    size_t position = 0;

    Parser(Analysis& analysis, std::string source) : result(analysis) {
        source = normalize(std::move(source));
        std::string token;
        for (size_t i = 0; i < source.size(); ++i) {
            if (std::isspace(static_cast<unsigned char>(source[i]))) {
                if (!token.empty()) { tokens.push_back(token); token.clear(); }
            } else if (source[i] == '(' || source[i] == ')' || source[i] == ',') {
                if (!token.empty()) { tokens.push_back(token); token.clear(); }
                if (source[i] != ',') tokens.emplace_back(1, source[i]);
            } else token += source[i];
        }
        if (!token.empty()) tokens.push_back(token);
    }

    int add(Kind kind, int left = -1, int right = -1, std::string atom = {}) {
        result.formulas.push_back({kind, std::move(atom), left, right});
        return static_cast<int>(result.formulas.size() - 1);
    }
    bool accept(const std::string& word) {
        if (position < tokens.size() && tokens[position] == word) { ++position; return true; }
        return false;
    }
    int expression() { return iff(); }
    int iff() {
        int value = implies();
        while (true) {
            const size_t saved = position;
            if ((accept("si") && accept("y") && accept("solo") && accept("si")) ||
                (accept("y") && accept("solo") && accept("si"))) {
                value = add(Kind::Iff, value, implies());
            } else {
                position = saved;
                break;
            }
        }
        return value;
    }
    int implies() {
        if (accept("si")) {
            const int condition = disjunction();
            if (!accept("entonces")) return -1;
            return add(Kind::Implies, condition, implies());
        }
        int value = disjunction();
        if (accept("entonces")) value = add(Kind::Implies, value, implies());
        return value;
    }
    int disjunction() {
        int value = conjunction();
        while (accept("o")) value = add(Kind::Or, value, conjunction());
        return value;
    }
    int conjunction() {
        int value = unary();
        while (position < tokens.size() && tokens[position] == "y" && (position + 1 >= tokens.size() || tokens[position + 1] != "solo")) {
            ++position;
            value = add(Kind::And, value, unary());
        }
        return value;
    }
    int unary() {
        if (accept("no")) return add(Kind::Not, unary());
        if (accept("(")) {
            int value = expression();
            if (!accept(")")) return -1;
            return value;
        }
        if (position >= tokens.size()) return -1;
        std::string atom;
        while (position < tokens.size() && tokens[position] != "y" && tokens[position] != "o" && tokens[position] != "entonces" && tokens[position] != "si" && tokens[position] != ")") {
            if (!atom.empty()) atom += ' ';
            std::string part = tokens[position++];
            atom += part;
        }
        if (atom.empty()) return -1;
        if (std::find(result.atoms.begin(), result.atoms.end(), atom) == result.atoms.end()) result.atoms.push_back(atom);
        return add(Kind::Atom, -1, -1, atom);
    }
};

int negate(Analysis& analysis, int index) {
    analysis.formulas.push_back({Kind::Not, "", index, -1});
    return static_cast<int>(analysis.formulas.size() - 1);
}

bool literal(const Analysis& analysis, int index, std::string& atom, bool& positive) {
    const auto& formula = analysis.formulas[index];
    if (formula.kind == Kind::Atom) { atom = formula.atom; positive = true; return true; }
    if (formula.kind == Kind::Not && analysis.formulas[formula.left].kind == Kind::Atom) { atom = analysis.formulas[formula.left].atom; positive = false; return true; }
    return false;
}

char letterFor(const Analysis& analysis, const std::string& atom) {
    const auto found = analysis.letters.find(atom);
    return found == analysis.letters.end() ? '?' : found->second;
}

void expand(Analysis& analysis, Branch branch, std::vector<Branch>& output) {
    for (size_t i = 0; i < branch.formulas.size(); ++i) {
        std::string atom; bool positive;
        if (!literal(analysis, branch.formulas[i], atom, positive)) continue;
        for (size_t j = i + 1; j < branch.formulas.size(); ++j) {
            std::string other; bool otherPositive;
            if (literal(analysis, branch.formulas[j], other, otherPositive) && atom == other && positive != otherPositive) {
                branch.closed = true;
                branch.steps.push_back({atom + " y ¬" + atom, "contradicción", true});
                output.push_back(std::move(branch));
                return;
            }
        }
    }
    for (size_t i = 0; i < branch.formulas.size(); ++i) {
        const int index = branch.formulas[i];
        const Formula formula = analysis.formulas[index];
        if (formula.kind == Kind::Atom || (formula.kind == Kind::Not && analysis.formulas[formula.left].kind == Kind::Atom)) continue;
        branch.steps.push_back({formulaText(analysis, index), "expandir", true});
        auto base = branch.formulas;
        base.erase(base.begin() + static_cast<long>(i));
        auto addNot = [&](int child) { return negate(analysis, child); };
        auto continueBranch = [&](std::vector<int> values) {
            Branch next = branch;
            next.formulas = std::move(values);
            expand(analysis, std::move(next), output);
        };
        if (formula.kind == Kind::And) {
            base.push_back(formula.left);
            base.push_back(formula.right);
            continueBranch(std::move(base));
            return;
        }
        if (formula.kind == Kind::Not) {
            const Formula child = analysis.formulas[formula.left];
            if (child.kind == Kind::Not) {
                base.push_back(child.left);
                continueBranch(std::move(base));
                return;
            }
            if (child.kind == Kind::Or || child.kind == Kind::Implies) {
                base.push_back(addNot(child.left));
                if (child.kind == Kind::Or) base.push_back(addNot(child.right));
                else base.push_back(child.right);
                continueBranch(std::move(base));
                return;
            }
            if (child.kind == Kind::And) {
                Branch one = branch;
                Branch two = branch;
                one.formulas = base;
                two.formulas = base;
                one.formulas.push_back(addNot(child.left));
                two.formulas.push_back(addNot(child.right));
                expand(analysis, std::move(one), output);
                expand(analysis, std::move(two), output);
                return;
            }
            if (child.kind == Kind::Iff) {
                Branch one = branch;
                Branch two = branch;
                one.formulas = base;
                two.formulas = base;
                one.formulas.push_back(child.left);
                one.formulas.push_back(addNot(child.right));
                two.formulas.push_back(addNot(child.left));
                two.formulas.push_back(child.right);
                expand(analysis, std::move(one), output);
                expand(analysis, std::move(two), output);
                return;
            }
        }
        Branch one = branch;
        Branch two = branch;
        one.formulas = base;
        two.formulas = base;
        if (formula.kind == Kind::Or) {
            one.formulas.push_back(formula.left);
            two.formulas.push_back(formula.right);
        } else if (formula.kind == Kind::Implies) {
            one.formulas.push_back(addNot(formula.left));
            two.formulas.push_back(formula.right);
        } else if (formula.kind == Kind::Iff) {
            one.formulas.push_back(formula.left);
            one.formulas.push_back(formula.right);
            two.formulas.push_back(addNot(formula.left));
            two.formulas.push_back(addNot(formula.right));
        }
        expand(analysis, std::move(one), output);
        expand(analysis, std::move(two), output);
        return;
    }
    output.push_back(std::move(branch));
}

} // namespace

Analysis solve(const std::vector<std::string>& texts) {
    Analysis analysis;
    for (const auto& text : texts) {
        Parser parser(analysis, text);
        const int root = parser.expression();
            if (root < 0 || parser.position != parser.tokens.size()) {
                analysis.error = "No pude interpretar: " + text;
                analysis.atoms.clear();
                analysis.letters.clear();
                analysis.rules.clear();
                analysis.formulas.clear();
                return analysis;
            }
        analysis.rules.push_back({text, root});
    }
    for (size_t i = 0; i < analysis.atoms.size(); ++i) analysis.letters[analysis.atoms[i]] = static_cast<char>('p' + i);
    Branch initial;
    for (const auto& rule : analysis.rules) initial.formulas.push_back(rule.formula);
    expand(analysis, std::move(initial), analysis.branches);
    for (const auto& branch : analysis.branches) {
        if (branch.closed) continue;
        std::map<std::string, bool> fixed;
        for (int index : branch.formulas) {
            std::string atom;
            bool positive = false;
            if (literal(analysis, index, atom, positive)) fixed[atom] = positive;
        }
        std::vector<std::string> missing;
        for (const auto& atom : analysis.atoms) if (!fixed.count(atom)) missing.push_back(atom);
        const std::size_t combinations = std::size_t{1} << missing.size();
        for (std::size_t mask = 0; mask < combinations; ++mask) {
            auto candidate = fixed;
            for (std::size_t bit = 0; bit < missing.size(); ++bit) candidate[missing[bit]] = (mask & (std::size_t{1} << bit)) != 0;
            bool valid = true;
            for (const auto& rule : analysis.rules) {
                if (!evaluate(analysis, rule.formula, candidate)) { valid = false; break; }
            }
            if (!valid) continue;
            if (std::find(analysis.models.begin(), analysis.models.end(), candidate) == analysis.models.end()) analysis.models.push_back(std::move(candidate));
        }
    }
    return analysis;
}

bool evaluate(const Analysis& analysis, int index, const std::map<std::string, bool>& values) {
    if (index < 0 || index >= static_cast<int>(analysis.formulas.size())) return false;
    const Formula& formula = analysis.formulas[index];
    if (formula.kind == Kind::Atom) {
        const auto found = values.find(formula.atom);
        return found != values.end() && found->second;
    }
    if (formula.kind == Kind::Not) return !evaluate(analysis, formula.left, values);
    if (formula.kind == Kind::And) return evaluate(analysis, formula.left, values) && evaluate(analysis, formula.right, values);
    if (formula.kind == Kind::Or) return evaluate(analysis, formula.left, values) || evaluate(analysis, formula.right, values);
    if (formula.kind == Kind::Implies) return !evaluate(analysis, formula.left, values) || evaluate(analysis, formula.right, values);
    return evaluate(analysis, formula.left, values) == evaluate(analysis, formula.right, values);
}

std::string formulaText(const Analysis& analysis, int index, bool parenthesize) {
    if (index < 0 || index >= static_cast<int>(analysis.formulas.size())) return "?";
    const auto& formula = analysis.formulas[index];
    std::string value;
    if (formula.kind == Kind::Atom) value = std::string(1, letterFor(analysis, formula.atom));
    else if (formula.kind == Kind::Not) value = "¬" + formulaText(analysis, formula.left, true);
    else { const char* symbol = formula.kind == Kind::And ? " ∧ " : formula.kind == Kind::Or ? " ∨ " : formula.kind == Kind::Implies ? " → " : " ↔ "; value = formulaText(analysis, formula.left, true) + symbol + formulaText(analysis, formula.right, true); }
    return parenthesize && formula.kind != Kind::Atom && formula.kind != Kind::Not ? "(" + value + ")" : value;
}

std::string branchModel(const Analysis& analysis, const Branch& branch) {
    std::map<std::string, bool> values;
    for (int index : branch.formulas) { std::string atom; bool positive; if (literal(analysis, index, atom, positive)) values[atom] = positive; }
    std::ostringstream result; bool first = true;
    for (const auto& [atom, value] : values) { if (!first) result << ", "; first = false; result << letterFor(analysis, atom) << " = " << (value ? "V" : "F"); }
    return result.str();
}

std::string modelText(const Analysis& analysis, const std::map<std::string, bool>& model) {
    std::ostringstream result;
    for (size_t i = 0; i < analysis.atoms.size(); ++i) {
        if (i > 0) result << ", ";
        const auto& atom = analysis.atoms[i];
        result << letterFor(analysis, atom) << " = " << (model.count(atom) && model.at(atom) ? "V" : "F");
    }
    return result.str();
}

} // namespace sat