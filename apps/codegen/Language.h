#ifndef TRS_CODEGEN_LANGUAGE_H
#define TRS_CODEGEN_LANGUAGE_H

#include "Halide.h"
#include "Printer.h"
#include <memory>
#include <vector>

using namespace Halide;
using namespace Halide::Internal;
using std::make_shared;
using std::shared_ptr;
using std::vector;

namespace Language {

enum class IRType {
    // Type checks
    Add,
    Sub,
    Mod,
    Mul,
    Div,
    Min,
    Max,
    EQ,
    NE,
    LT,
    LE,
    GT,
    GE,
    And,
    Or,
    Not,
    Select,
    IntImm,
    Broadcast,
    Ramp,

    // Stmt
    Equality,
    Return,
    Condition,
    Sequence,
};

struct Node {
    virtual void print(std::ostream &stream, std::string indent) const = 0;  // This makes the struct abstract.
    virtual bool equal(const shared_ptr<Node> &other) const = 0;
    virtual ~Node() = default;  // Otherwise C++ breaks for some reason.

    vector<shared_ptr<Node>> children;
    const IRType type;

    Node(IRType _type)
        : type(_type) {
    }

    template<typename T>
    const T *as(IRType _type) const {
        if (type != _type) {
            return nullptr;
        } else {
            return dynamic_cast<const T *>(this);
        }
    }

    // Might want to make this virtual so Return nodes can override it and fail early.
    template<typename T>  // T must inherit from Node.
    shared_ptr<T> get_child(shared_ptr<T> _child) {
        auto is_node = [&_child](const shared_ptr<Node> &child) { return _child->equal(child); };
        auto result = std::find_if(children.begin(), children.end(), is_node);
        if (result != children.end()) {
            // This is safe, I think?
            return std::dynamic_pointer_cast<T>(*result);
        } else {
            // Need to insert the child
            children.push_back(_child);
            return _child;
        }
    }
};

template<typename T>
struct TypeCheck : public Node {
    std::string current_name;
    std::string output_name;

    bool equal(const shared_ptr<Node> &other) const override {
        if (const T *other_tc = other->as<T>(type)) {
            // We only care about the object's name (and type of course)
            return (current_name == other_tc->current_name);
        } else {
            return false;
        }
    }

    TypeCheck(IRType _type, const std::string &_curr, const std::string &_out)
        : Node(_type), current_name(_curr), output_name(_out) {
    }

    // TODO: this could probably be manually inlined below.
    const std::string get_type_name() const {
        return T::type_name;
    }

    void print(std::ostream &stream, std::string indent) const override {
        const std::string type_name = get_type_name();
        std::string str_cond = Printer::make_type_checker_condition(current_name, type_name, output_name);
        stream << indent << "if (" << str_cond << ") {\n";
        for (const auto &child : children) {
            child->print(stream, indent + "  ");
        }
        stream << indent << "}\n";
    }
};

struct Add final : public TypeCheck<Add> {
    Add(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::Add, _curr, _out) {
    }
    inline static const std::string type_name = "Add";
};

struct Sub final : public TypeCheck<Sub> {
    Sub(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::Sub, _curr, _out) {
    }
    inline static const std::string type_name = "Sub";
};

struct Mod final : public TypeCheck<Mod> {
    Mod(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::Mod, _curr, _out) {
    }
    inline static const std::string type_name = "Mod";
};

struct Mul final : public TypeCheck<Mul> {
    Mul(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::Mul, _curr, _out) {
    }
    inline static const std::string type_name = "Mul";
};

struct Div final : public TypeCheck<Div> {
    Div(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::Div, _curr, _out) {
    }
    inline static const std::string type_name = "Div";
};

struct Min final : public TypeCheck<Min> {
    Min(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::Min, _curr, _out) {
    }
    inline static const std::string type_name = "Min";
};

struct Max final : public TypeCheck<Max> {
    Max(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::Max, _curr, _out) {
    }
    inline static const std::string type_name = "Max";
};

struct EQ final : public TypeCheck<EQ> {
    EQ(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::EQ, _curr, _out) {
    }
    inline static const std::string type_name = "EQ";
};

struct NE final : public TypeCheck<NE> {
    NE(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::NE, _curr, _out) {
    }
    inline static const std::string type_name = "NE";
};

struct LT final : public TypeCheck<LT> {
    LT(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::LT, _curr, _out) {
    }
    inline static const std::string type_name = "LT";
};

struct LE final : public TypeCheck<LE> {
    LE(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::LE, _curr, _out) {
    }
    inline static const std::string type_name = "LE";
};

struct GT final : public TypeCheck<GT> {
    GT(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::GT, _curr, _out) {
    }
    inline static const std::string type_name = "GT";
};

struct GE final : public TypeCheck<GE> {
    GE(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::GE, _curr, _out) {
    }
    inline static const std::string type_name = "GE";
};

struct And final : public TypeCheck<And> {
    And(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::And, _curr, _out) {
    }
    inline static const std::string type_name = "And";
};

struct Or final : public TypeCheck<Or> {
    Or(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::Or, _curr, _out) {
    }
    inline static const std::string type_name = "Or";
};

struct Not final : public TypeCheck<Not> {
    Not(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::Not, _curr, _out) {
    }
    inline static const std::string type_name = "Not";
};

struct Select final : public TypeCheck<Select> {
    Select(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::Select, _curr, _out) {
    }
    inline static const std::string type_name = "Select";
};

struct Broadcast final : public TypeCheck<Broadcast> {
    Broadcast(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::Select, _curr, _out) {
    }
    inline static const std::string type_name = "Broadcast";
};

struct Ramp final : public TypeCheck<Ramp> {
    Ramp(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::Select, _curr, _out) {
    }
    inline static const std::string type_name = "Ramp";
};

struct IntImm final : public TypeCheck<IntImm> {
    IntImm(const std::string &_curr, const std::string &_out)
        : TypeCheck(IRType::IntImm, _curr, _out) {
    }
    inline static const std::string type_name = "IntImm";
};

struct Equality final : public Node {
    std::string name1, name2;
    Equality(const std::string &_name1, const std::string &_name2)
        : Node(IRType::Equality), name1(_name1), name2(_name2) {
    }
    bool equal(const shared_ptr<Node> &other) const override;
    void print(std::ostream &stream, std::string indent) const override;
};

struct Return final : public Node {
    std::string retval;
    Return(const std::string &_retval)
        : Node(IRType::Return), retval(_retval) {
    }
    bool equal(const shared_ptr<Node> &other) const override;
    void print(std::ostream &stream, std::string indent) const override;
};

// Used as a generic condition, makes a lot of stuff easier. Probably could have just inherited from this.
struct Condition final : public Node {
    std::string condition;
    Condition(const std::string &_condition)
        : Node(IRType::Condition), condition(_condition) {
    }
    bool equal(const shared_ptr<Node> &other) const override;
    void print(std::ostream &stream, std::string indent) const override;
};

// Used as the top level node *ONLY*
struct Sequence final : public Node {
    Sequence()
        : Node(IRType::Sequence) {
    }
    bool equal(const shared_ptr<Node> &other) const override;
    void print(std::ostream &stream, std::string indent) const override;
};

}  // namespace Language

#endif