#include "Rule.h"

void Rule::set_allowed_types(std::vector<NumericType> _allowed_types){
    allowed_types = _allowed_types;
}
std::vector<NumericType> Rule::get_allowed_types(){
    return allowed_types;
}

void Rule::set_disallowed_types(std::vector<NumericType> _disallowed_types){
    disallowed_types = _disallowed_types;
}
std::vector<NumericType> Rule::get_disallowed_types(){
    return disallowed_types;
}