#include "Language.h"

using namespace Halide;
using namespace Halide::Internal;
using std::make_shared;
using std::shared_ptr;
using std::vector;

namespace Language {


bool Equality::equal(const shared_ptr<Node> &other) const {
    if (const Equality *other_equal = other->as<Equality>(IRType::Equality)) {
        return (name1 == other_equal->name1) && (name2 == other_equal->name2);
    } else {
        return false;
    }
}

void Equality::print(std::ostream &stream, std::string indent) const {
    stream << indent << "if (equal(" << name1 << ", " << name2 << ")) {\n";
    for (const auto &child : children) {
        child->print(stream, indent + "  ");
    }
    stream << indent << "}\n";
}

bool Return::equal(const shared_ptr<Node> &other) const {
    if (const Return *other_return = other->as<Return>(IRType::Return)) {
        return (retval == other_return->retval);
    } else {
        return false;
    }
}

void Return::print(std::ostream &stream, std::string indent) const {
    assert(children.empty());  // Return nodes should never have children.
    stream << indent << "return " << retval << ";\n";
}

bool Condition::equal(const shared_ptr<Node> &other) const {
    if (const Condition *other_c = other->as<Condition>(IRType::Condition)) {
        return condition == other_c->condition;
    } else {
        return false;
    }
}

void Condition::print(std::ostream &stream, std::string indent) const {
    stream << indent << "if (" << condition << ") {\n";
    for (const auto &child : children) {
        child->print(stream, indent + "  ");
    }
    stream << indent << "}\n";
}

bool Sequence::equal(const shared_ptr<Node> &other) const {
    assert(false);  // Should never be compared to other nodes.
}

void Sequence::print(std::ostream &stream, std::string indent) const {
    for (const auto &child : children) {
        child->print(stream, indent + "  ");
    }
}
}  // namespace Language