# Base class for all operators
class Operator:
    pass

class Var:
    def __init__(self, name):
        self.name = name

    def __2str__(self):
        return self.name

class Pred(Operator):
    def __init__(self, predicate, variables):
        self.predicate = predicate
        self.name = str(predicate)
        self.variables = variables
        self.len = len(variables)

    def __2str__(self):
        if self.len > 0:
            return f"{self.name}({','.join(v.name for v in self.variables)})"
        else:
            return f"{self.name}()"

class Equal(Operator):
    def __init__(self, var1, var2):
        self.var1 = var1
        self.var2 = var2


class Less(Operator):
    def __init__(self, var1, var2):
        self.var1 = var1
        self.var2 = var2


class LessEq(Operator):
    def __init__(self, var1, var2):
        self.var1 = var1
        self.var2 = var2

class Neg(Operator):
    def __init__(self, operator):
        self.operator = operator

class And(Operator):
    def __init__(self, operator1, operator2):
        self.operator1 = operator1
        self.operator2 = operator2


class Or(Operator):
    def __init__(self, operator1, operator2):
        self.operator1 = operator1
        self.operator2 = operator2


class Implies(Operator):
    def __init__(self, operator1, operator2):
        self.operator1 = operator1
        self.operator2 = operator2


class Exists(Operator):
    def __init__(self, var, operator):
        self.var = var
        self.operator = operator


class ForAll(Operator):
    def __init__(self, var, operator):
        self.var = var
        self.operator = operator


class Prev(Operator):
    def __init__(self, interval, operator):
        self.interval = interval
        self.operator = operator


class Next(Operator):
    def __init__(self, interval, operator):
        self.interval = interval
        self.operator = operator


class Eventually(Operator):
    def __init__(self, interval, operator):
        self.interval = interval
        self.operator = operator


class Once(Operator):
    def __init__(self, interval, operator):
        self.interval = interval
        self.operator = operator


class Since(Operator):
    def __init__(self, interval, operator1, operator2):
        self.interval = interval
        self.operator1 = operator1
        self.operator2 = operator2


class Until(Operator):
    def __init__(self, interval, operator1, operator2):
        self.interval = interval
        self.operator1 = operator1
        self.operator2 = operator2

        
class NotUntil:
    def __init__(self, interval, operator1, operator2):
        self.interval = interval
        self.operator1 = operator1
        self.operator2 = operator2


class Aggreg:
    def __init__(self, operator, y, z, group_vars, formula):
        self.operator = operator
        self.y = y
        self.z = z
        self.group_vars = group_vars
        self.formula = formula

class Let:
    def __init__(self, pred, varlist, operator1, operator2):
        self.predicate = pred
        self.varlist = varlist
        self.operator1 = operator1
        self.operator2 = operator2

