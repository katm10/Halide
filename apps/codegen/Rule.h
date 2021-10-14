#ifndef TRS_CODEGEN_RULE
#define TRS_CODEGEN_RULE

#include <string>
#include <vector>

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
    /*
        TODO: this should really be
            const Expr before;
            const Expr after;
            const Cond pred;
        TODO: this should not all be public
    */
    const std::string rule;
    std::vector<NumericType> allowed_types;
    std::vector<NumericType> disallowed_types;

    ~Rule() = default;
    Rule(const std::string _rule)
        : rule(_rule) {
    }

    void set_allowed_types(std::vector<NumericType> _allowed_types);
    std::vector<NumericType> get_allowed_types();

    void set_disallowed_types(std::vector<NumericType> _disallowed_types);
    std::vector<NumericType> get_disallowed_types();
};

#endif