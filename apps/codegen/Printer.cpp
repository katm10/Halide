#include "Printer.h"

using namespace Halide;
using namespace Halide::Internal;

// For code generation

std::string Printer::make_type_checker_condition(const std::string &var_name, const std::string &type_name, const std::string &output_name) {
    return "const " + type_name + " *" + output_name + " = " + var_name + ".as<" + type_name + ">()";
}

std::string Printer::make_new_unique_name() {
    static int counter = 0;
    return "a" + std::to_string(counter++);
}

void Printer::IRPrinterNoType::visit(const Variable *op) {
    stream << op->name;
}

void Printer::IRPrinterNoType::visit(const Call *op) {
    stream << op->name << "(";
    IRPrinter::print_list(op->args);
    stream << ")";
}

// TODO: print in proper C++/Halide (probably)
// Printer::IRPrinterNoType::visit(const Cast *op) {
// }

std::string Printer::pretty_print(const Expr &expr) {
    std::stringstream s;
    IRPrinterNoType printer = s;
    expr.accept(&printer);
    return s.str();
}

std::string Printer::build_expr(const Expr &expr, const VarScope &scope) {
    std::map<std::string, Expr> replacements;
    for (const auto &p : scope) {
        replacements[p.first] = Variable::make(p.second.type, p.second.name);
    }
    // TODO: the old method asserted that all variables that exist in `expr` have a match in `scope`,
    //       we should do that here too.
    Expr new_expr = Halide::Internal::substitute(replacements, expr);
    return pretty_print(new_expr);
}