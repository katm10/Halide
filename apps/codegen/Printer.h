#ifndef TRS_CODEGEN_PRINTER_H
#define TRS_CODEGEN_PRINTER_H

#include <string>
#include <vector>

#include "Halide.h"

using namespace Halide;
using namespace Halide::Internal;

struct VarInfo {
    Halide::Type type;
    std::string name;
    VarInfo(Halide::Type _type, const std::string &_name)
        : type(_type), name(_name) {
    }
    VarInfo() {
        assert(false);  // This should never happen.
        // TODO: how to properly do this.
    }
};

typedef std::map<std::string, VarInfo> VarScope;

namespace Printer {

// For code generation
std::string make_type_checker_condition(const std::string &var_name, const std::string &type_name, const std::string &output_name);
std::string make_new_unique_name();

std::string pretty_print(const Expr &expr);
std::string build_expr(const Expr &expr, const VarScope &scope);

class IRPrinterNoType : public IRPrinter {
public:
    IRPrinterNoType(std::ostream &stream)
        : IRPrinter(stream) {
    }

protected:
    void visit(const Variable *op) override;
    void visit(const Call *op) override;
};

}  // namespace Printer

#endif