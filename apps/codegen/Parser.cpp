#include "Rule.h"
#include <cassert>
#include <fstream>
#include <iostream>
#include <stdio.h>

// TODO: this should really be a class
std::vector<Rule> rules;
const char *cursor, *end;

bool is_whitespace(char c) {
    return c == ' ' || c == '\t';
}

void consume_whitespace(const char **cursor, const char *end) {
    while (*cursor < end && is_whitespace(**cursor)) {
        (*cursor)++;
    }
}

bool consume(const char **cursor, const char *end, const char *expected) {
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

void expect(const char **cursor, const char *end, const char *pattern) {
    if (!consume(cursor, end, pattern)) {
        printf("Parsing failed. Expected %s, got %s\n",
               pattern, *cursor);
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
    expect(&cursor, end, "rewrite");
    expect(&cursor, end, "(");
    // TODO: create an expr and cond parser instead of this
    std::string rule = "";
    int paren = 0;
    while (paren != 0 || *cursor != ')') {
        rule += *cursor;
        if (*cursor == ')') {
            paren--;
        } else if (*cursor == '(') {
            paren++;
        }
        cursor++;
    }
    return rule;
}

std::vector<Rule> parse_rules_from_file(const std::string &filename) {

    size_t filesize = get_filesize(filename);

    char byte = 0;
    char cfile[filesize];

    std::ifstream input_file(filename);
    assert(input_file.is_open());

    // TODO: support comments
    for(size_t i = 0; i < filesize; i++){
        input_file.get(byte);
        cfile[i] = byte;
    }

    cursor = cfile;
    end = cursor + filesize;
    
    std::string rule = parse_r();
    std::cout << rule << std::endl;

    return rules;
}

int main() {
    std::string filename = "parser_input/good1.txt";  // TODO take this from std::cin instead
    std::vector<Rule> rules = parse_rules_from_file(filename);
}