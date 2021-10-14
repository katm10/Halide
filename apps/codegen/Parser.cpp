#include "Rule.h"
#include <cassert>
#include <fstream>
#include <iostream>
#include <map>
#include <stdio.h>
#include <tuple>
#include <memory>
#include "Halide.h" // TODO delete this, using for the Expr/Type types

using Halide::Expr;
using Halide::Type;

void log(const std::string debug_info, const int line) {
    std::cout << debug_info << "\nLine: " << line << std::endl;
}

// TODO: this should really be a class
const char **cursor, *end;
std::vector<std::pair<Expr, int>> stack;

// TODO: I don't like this solution very much, also probably missing a significant number of possible types
// switch to flags, refer to CodeGen_ARM ~l200
const std::map<std::string, NumericType> typeStrings{
    {"uint", NumericType::UINT},
    {"int", NumericType::INT},
    {"float", NumericType::FLOAT},
    {"no_overflow", NumericType::NO_OVERFLOW},
    {"no_overflow_int", NumericType::NO_OVERFLOW_INT},
    {"bool", NumericType::BOOL}};

bool is_whitespace(char c) {
    return c == ' ' || c == '\t';
}

// TODO: I never actually use this but I most definitely should
void consume_whitespace() {
    while (*cursor < end && is_whitespace(**cursor)) {
        (*cursor)++;
    }
}

bool consume(const char *expected) {
    const char *tmp = *cursor;
    while (*tmp == *expected && tmp < end && *expected) {
        tmp++;
        expected++;
    }
    if ((*expected) == 0) {
        *cursor = tmp;
        return true;
    } else {
        return false;
    }
}

void expect(const char *pattern) {
    if (!consume(pattern)) {
        std::cerr << "why\n";
        std::cerr << "Parsing failed. Expected " << pattern << ", got " << *cursor << "\n";
        // printf("Parsing failed. Expected %s, got %s",
        //        pattern, *cursor);
        abort();
    }
}

// TODO: how portable is this?
size_t get_filesize(const std::string &filename) {
    std::ifstream file(filename, std::ios::binary | std::ios::ate);
    size_t filesize = file.tellg();
    file.close();

    return filesize;
}

// TODO: this needs to parse much more finely
std::string parse_r() {
    expect("rewrite(");
    // TODO: create an expr and cond parser instead of this
    std::string rule = "";
    int paren = 0;
    while (paren != 0 || **cursor != ')') {
        rule += **cursor;
        if (**cursor == ')') {
            paren--;
        } else if (**cursor == '(') {
            paren++;
        }
        cursor++;
    }
    expect(")");

    return rule;
} 

NumericType parse_type() {
    for (const auto typePair : typeStrings) {
        if (consume(typePair.first.c_str())) {
            return typePair.second;
        }
    }
    assert(0);  // we should not get here
}

std::tuple<bool, std::vector<NumericType>> parse_types() {
    bool allowed = true;
    std::vector<NumericType> types;

    if (consume("!")) {
        allowed = false;
        expect("(");
    }

    // is there a more efficient way to do this?
    types.push_back(parse_type());
    while (consume(",")) {
        types.push_back(parse_type());
    }

    if (!allowed) {
        expect(")");
    }

    return std::tuple<bool, std::vector<NumericType>>(allowed, types);
}

std::vector<Rule> parse_rules() {
    std::vector<Rule> rules;

    while (*cursor < end) {
        // Parse R
        if (consume("(")) {
            // Parse G
            std::vector<std::string> rulestrs;
            rulestrs.push_back(parse_r());
            while (consume("\n")) {
                rulestrs.push_back(parse_r());
            }
            expect(")");
            expect("|-");
            std::tuple<bool, std::vector<NumericType>> types_tuple = parse_types();

            for (const auto rulestr : rulestrs) {
                Rule r(rulestr);                 // should I have used a pointer here instead?
                if (std::get<0>(types_tuple)) {  // these are allowed types
                    r.set_allowed_types(std::get<1>(types_tuple));
                } else {
                    r.set_disallowed_types(std::get<1>(types_tuple));
                }
                rules.push_back(r);
            }
        } else {
            Rule r(parse_r());  // TODO I need a lot of error checking oops
            if (consume("|-")) {
                // TODO this could be more modular

                std::tuple<bool, std::vector<NumericType>> types_tuple = parse_types();
                if (std::get<0>(types_tuple)) {  // these are allowed types
                    r.set_allowed_types(std::get<1>(types_tuple));
                } else {
                    r.set_disallowed_types(std::get<1>(types_tuple));
                }
            }
            rules.push_back(r);
        }
        consume("\n");
    }
    return rules;
}

std::vector<Rule> parse_rules_from_file(const std::string &filename) {
    size_t filesize = get_filesize(filename);

    char byte = 0;
    char cfile[filesize];

    std::ifstream input_file(filename);
    assert(input_file.is_open());

    // TODO: support comments
    size_t i = 0;
    while (input_file.get(byte)) {
        if (!(byte == ' ' || byte == '\t')) {
            cfile[i] = byte;
            i++;
        }
    }
    const char *start = cfile;
    cursor = &start;
    end = cfile + i;

    return parse_rules();
}

int main() {
    std::string filename;
    std::cin >> filename;
    std::vector<Rule> rules = parse_rules_from_file(filename);

    for (const Rule r : rules) {
        std::cout << "Rule: " << r.rule << std::endl;
    }
}