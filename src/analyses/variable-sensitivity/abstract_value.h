/*******************************************************************\

 Module: Analyses Variable Sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_VALUE_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_VALUE_H

#include <analyses/variable-sensitivity/abstract_object.h>


class abstract_valuet:public abstract_objectt
{
public:
 abstract_valuet(const typet &type);
 abstract_valuet(const typet &type, bool top, bool bottom);
 abstract_valuet(const abstract_valuet &old);
 abstract_valuet(const constant_exprt &expr);

 CLONE
 MERGE(abstract_objectt)
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_VALUE_H