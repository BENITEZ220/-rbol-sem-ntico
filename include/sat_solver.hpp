#pragma once

#include <map>
#include <string>
#include <vector>

namespace sat {

enum class Kind { Atom, Not, And, Or, Implies, Iff };

struct Formula {
    Kind kind;
    std::string atom;
    int left = -1;
    int right = -1;
};

struct Rule { std::string text; int formula = -1; };
struct BranchStep { std::string expression; std::string rule; bool expanded = false; };
struct Branch { std::vector<int> formulas; std::vector<BranchStep> steps; bool closed = false; };

struct Analysis {
    std::vector<std::string> atoms;
    std::map<std::string, char> letters;
    std::vector<Rule> rules;
    std::vector<Formula> formulas;
    std::vector<Branch> branches;
    std::vector<std::map<std::string, bool>> models;
    std::string error;
};

Analysis solve(const std::vector<std::string>& texts);
std::string formulaText(const Analysis& analysis, int index, bool parenthesize = false);
std::string branchModel(const Analysis& analysis, const Branch& branch);
bool evaluate(const Analysis& analysis, int index, const std::map<std::string, bool>& values);
std::string modelText(const Analysis& analysis, const std::map<std::string, bool>& model);

} // namespace sat