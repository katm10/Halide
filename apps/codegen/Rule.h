#ifndef TRS_CODEGEN_RULE
#define TRS_CODEGEN_RULE

#include <string>
#include <vector>
#include "Halide.h" // TODO remove

enum NumericType {
    UINT,
    INT,
    FLOAT,
    NO_OVERFLOW,
    NO_OVERFLOW_INT,
    BOOL
    // TODO almost certainly missing a lot here
};

class Rule {
public:
    // TODO: this should not all be public
    const Halide::Expr before;
    const Halide::Expr after;
    const Halide::Expr pred;
    // TODO fix this
    std::vector<NumericType> allowed_types;
    std::vector<NumericType> disallowed_types;

    ~Rule() = default;
    Rule(){}
    Rule(const Halide::Expr _before, const Halide::Expr _after)
        : before(_before), after(_after) {}

    Rule(const Halide::Expr _before, const Halide::Expr _after, const Halide::Expr _pred)
        : before(_before), after(_after), pred(_pred) {}

    void set_allowed_types(std::vector<NumericType> _allowed_types);
    std::vector<NumericType> get_allowed_types();

    void set_disallowed_types(std::vector<NumericType> _disallowed_types);
    std::vector<NumericType> get_disallowed_types();
};

#endif