import random
from src.operators import *

class FormulaGenerator:
    """
    FormulaGenerator class
    Contains methods to generate random formulas
    """
    def __init__(self, sig, size, seed, ub_fv=None, weights=None):
        """
        Initialize FormulaGenerator
        Arguments:
            sig: Signature object
            size: int
            seed: int
            ub_fv: int
            weights: dict
            
        Returns:
            FormulaGenerator object
        """
        self.sig = sig
        self.size = size
        self.max_arity = sig.max_arity
        self.min_arity = sig.min_arity
        self.upper_bound_fv = sig.max_arity if ub_fv is None else ub_fv 
        self.all_variables = set([Var(f"x{i}") for i in range(1, max(2,self.upper_bound_fv+1))]) 
        self.y_counter = 0
        self.z_counter = 0
        self.let_counter = 1

        self.required_pred = set()
        self.no_empty = self.min_arity != 0

        self.seed = seed

        self.rng = random.Random()
        if seed is None:
            self.rng.seed()
        else:
            self.rng.seed(seed)

        if self.upper_bound_fv < self.min_arity:
            print("__________\nWarning: upper bound of free variables is less than the minimum arity of predicates.")
            print(f"Temporary fix: upping the upper bound of free variables to {self.min_arity}.\n__________")
            self.upper_bound_fv = self.min_arity
            self.all_variables = set([Var(f"x{i}") for i in range(1, self.upper_bound_fv+1)])

        if weights is None:
            self.weights = {
                'And': 0.1, 
                'Or': 0.1,
                'Prev': 0.1, 
                'Once': 0.1, 
                'Next': 0.1,
                'Eventually': 0.1,
                'Since': 0.1, 
                'Until': 0.1,
                'Rand': 0.1, 
                'Eand': 0.1, 
                'Nand': 0.1,
                'Exists': 0.1,
                'Aggreg': 0.1,
                'Let': 0.1
            }
        else:
            self.weights = weights

    def random_var(self, n=1, lb=None, ub=None):
        """
        Return n variables from a given free variable set.
        Ensures the number of variables respects the lower and upper bounds.
        """
        if lb is None:
            lb = []
        else:
            lb = sorted(lb, key=lambda x: x.name)

        if ub is None:
            ub = sorted(self.all_variables, key=lambda x: x.name)
            ub += [v for v in lb if v not in ub]
            ub = sorted(ub, key=lambda x: x.name)
        else:
            ub = sorted(ub, key=lambda x: x.name)
        if len(lb) < n:
            if len(lb) == 0 and len(ub) == 0:
                sorted_new_var = sorted(self.all_variables, key=lambda x: x.name)
                return self.rng.sample(sorted_new_var, n)
            elif len(lb) == 0 and len(ub) >= n:
                return self.rng.sample(ub, k=n)
            else:
                frs = self.rng.sample(lb, k=len(lb))
                remaining = n - len(lb)

                a = remaining//len(ub)
                b = remaining%len(ub)
                snd = []
                for _ in range(a):
                    snd += self.rng.sample(ub, k=max(len(ub),1))
                snd += self.rng.sample(ub, k=b)
                return frs+snd
        else:
            frs = self.rng.sample(lb, k=n)
            return frs

    def random_pred(self, lb=None, ub=None):
        """
        Return a Pred instance with variables from free_vars.
        Respects the bounds on free variables.
        """
        if lb is None:
            lb = set()
        if ub is None:
            ub = lb.union(self.all_variables) if lb!=set() else self.all_variables

        if len(self.required_pred) != 0 and len(ub) > 0:
            pred = self.rng.choice([p for p in self.sig.predicates if p in self.required_pred])
            self.required_pred.remove(pred)
            if len(lb) > pred.len:
                sorted_lb = sorted(lb, key=lambda x: x.name)
                vars_in_pred = set(sorted_lb[:pred.len])
                formula = Pred(pred.name, vars_in_pred)
                for v in sorted_lb[pred.len:]:
                    t = self.random_const()
                    formula = And(formula, Equal(v, t))
                return formula, sorted_lb

            vars_in_pred = self.random_var(pred.len, lb=lb, ub=ub)
            formula = Pred(pred.name, vars_in_pred)
            return formula, vars_in_pred
        if len(lb) > self.max_arity:
            pred = self.rng.choice([p for p in self.sig.predicates if p.len == self.max_arity])
            sorted_lb = sorted(lb, key=lambda x: x.name)
            vars_in_pred = set(sorted_lb[:pred.len])
            formula = Pred(pred.name, vars_in_pred)
            for v in sorted_lb[pred.len:]:
                t = self.random_const()
                formula = And(formula, Equal(v, t))
            return formula, sorted_lb

        if len(ub)>0:
            required_bound = [p for p in self.sig.predicates if p.len >= len(lb)]
        else:
            required_bound = [p for p in self.sig.predicates if p.len >= len(lb) and p.len <= len(ub)]
        if required_bound != []:
            pred = self.rng.choice(required_bound)
        else:
            try:
                pred = self.rng.choice([p for p in self.sig.predicates if p.len >= len(lb)])
            except Exception as e:
                print(f"Error: {e}")
                pred = self.rng.choice([p for p in self.sig.predicates if p.len == self.max_arity])
        vars_in_pred = self.random_var(pred.len, lb=lb, ub=ub)
        formula = Pred(pred.name, vars_in_pred)
        return formula, vars_in_pred

    def random_const(self):
        """Random constant."""
        return str(self.rng.randint(0, 100))

    def random_interval(self, left_lb=0, left_ub=5, delta=30, is_bound=False):
        """Random interval."""
        start = self.rng.randint(left_lb, left_ub)
        if is_bound:
            inf_intv = False
        else:
            inf_intv = self.rng.choice([True, False])
        if inf_intv:
            end = None
        else:
            end = self.rng.randint(start+1, start+delta)
        return (start, end)

    def generate(self, size=None, fv_lb = None, fv_ub = None):
        """Generate a random formula."""
        if size is None:
            size = self.size
        if fv_lb is None:
            fv_lb = set()
        if fv_ub is None:
            fv_ub = self.all_variables.union(fv_lb)
        if len(fv_lb) == 0 and len(fv_ub) == 0 and self.no_empty:
            self.y_counter += 1
            var = Var(f"y{self.y_counter}")
            formula, fv = self.generate(size, fv_lb={var}, fv_ub={var})

            return Exists(var, formula), fv-{var}

        if size == 0:
            formula, variables = self.random_pred(lb=fv_lb.copy(), ub=fv_ub.copy())
            return formula, set(variables)
        else:
            formula_choice = self.rng.choices(list(self.weights.keys()), weights=list(self.weights.values()))[0]

            if formula_choice == 'And':
                formula, fv = generate_and(self, size, fv_lb.copy(), fv_ub.copy())
                return formula, fv

            elif formula_choice == 'Rand':
                formula, fv = generate_and_with_relation(self, size, fv_lb.copy(), fv_ub.copy())
                return formula, fv

            elif formula_choice == 'Eand':
                formula, fv = generate_and_with_equality(self, size, fv_lb.copy(), fv_ub.copy())
                return formula, fv

            elif formula_choice == 'Nand':
                formula, fv = generate_and_negate(self, size, fv_lb.copy(), fv_ub.copy())
                return formula, fv

            elif formula_choice == 'Or':
                formula, fv = generate_or(self, size, fv_lb.copy(), fv_ub.copy())
                return formula, fv

            elif formula_choice in ['Since', 'Until']:
                formula, fv = generate_since_until(self, size, fv_lb.copy(), fv_ub.copy(), formula_choice)
                return formula, fv

            elif formula_choice in ['Prev', 'Once', 'Next', 'Eventually']:
                formula, fv = generate_prev_once(self, size, fv_lb.copy(), fv_ub.copy(), formula_choice)
                return formula, fv

            elif formula_choice == 'Exists':
                formula, fv = generate_exists(self, size, fv_lb.copy(), fv_ub.copy())
                return formula, fv

            elif formula_choice == 'Aggreg':
                formula, fv = generate_aggregation(self, size, fv_lb.copy(), fv_ub.copy())
                return formula, fv

            elif formula_choice == 'Let':
                formula, fv = generate_let(self, size, fv_lb.copy(), fv_ub.copy())
                return formula, fv

            else:
                raise ValueError(f"Unknown formula type chosen: {formula_choice}")

def generate_and(generator, size, lb, ub):
    """
    Generate an And formula
    And formula
    
    Args:
        generator (FormulaGenerator): Generator object
        size (int): remaining size of the formula
        lb (set): Lower bound of free variables
        ub (set): Upper bound of free variables
        
    Returns:
        Operator object: And object
    """
    new_size = (size - 1) // 2
    sorted_lb = sorted(lb, key=lambda x: x.name)
    frst_lb = set(sorted_lb[:len(sorted_lb)//2])
    scnd_lb = set(sorted_lb[len(sorted_lb)//2:])
    subformula1, fv1 = generator.generate(new_size, fv_lb=frst_lb, fv_ub=ub)
    subformula2, fv2 = generator.generate(new_size, fv_lb=scnd_lb, fv_ub=ub)
    formula = And(subformula1, subformula2)

    return formula, fv1.union(fv2)

def generate_and_negate(generator, size, lb, ub):
    """
    Generate an And formula with a negated subformula
    And formula with negated subformula
    
    Args:
        generator (FormulaGenerator): Generator object
        size (int): remaining size of the formula
        lb (set): Lower bound of free variables
        ub (set): Upper bound of free variables
        
    Returns:
        Operator object: And object with negated subformula
    """
    new_size = (size - 1) // 2
    subformula1, fv1 = generator.generate(new_size, fv_lb=lb, fv_ub=ub)
    subformula2, fv2 = generator.generate(new_size, fv_lb=set(),fv_ub=fv1.copy())

    formula = And(subformula1, Neg(subformula2))
    return formula, fv1.union(fv2)


def generate_or(generator, size, lb, ub):
    """
    Generate an Or formula
    Or formula
    
    Args:
        generator (FormulaGenerator): Generator object
        size (int): remaining size of the formula
        lb (set): Lower bound of free variables
        ub (set): Upper bound of free variables

    Returns:
        Operator object: Or object
    """
    new_size = (size - 1) // 2
    subformula1, fv1 = generator.generate(new_size, fv_lb=lb, fv_ub=ub)
    subformula2, fv2 = generator.generate(new_size, fv_lb=fv1.copy(), fv_ub=fv1.copy())

    formula = Or(subformula1, subformula2)
    return formula, fv1.union(fv2)

def generate_since_until(generator, size, lb, ub, op):
    """
    Generate a Since or Until formula
    Since formula or Until formula
    
    Args:
        generator (FormulaGenerator): Generator object
        size (int): remaining size of the formula
        lb (set): Lower bound of free variables
        ub (set): Upper bound of free variables
        op (str): Chosen opperator either: 'Since' or 'Until'
    Returns:
        Operator object: Since object or Until: Until object
    """
    new_size = (size - 1) // 2
    interval = generator.random_interval(is_bound=op=='Until')

    subformula_beta, fv_beta = generator.generate(new_size, fv_lb=lb, fv_ub=ub)
    subformula_alpha, fv_alpha = generator.generate(new_size, fv_lb=set(), fv_ub=fv_beta.copy())

    formula_class = Since if op == 'Since' else Until
    formula = formula_class(interval, subformula_alpha, subformula_beta)
    return formula, fv_beta.union(fv_alpha)

def generate_prev_once(generator, size, lb, ub, op):
    """
    Generate a Prev, Once, Next, Eventually formula
    Prev formula or Once formula
    
    Args:
        generator (FormulaGenerator): Generator object
        size (int): remaining size of the formula
        lb (set): Lower bound of free variables
        ub (set): Upper bound of free variables
        op (str): Chosen opperator either: 'Prev' or 'Once'
    Returns:
        Operator object: Prev object or Once: Once object
    """
    interval = generator.random_interval(is_bound=op in ['Eventually', 'Next'])
    subformula, fv = generator.generate(size - 1, fv_lb=lb, fv_ub=ub)
    if op == 'Prev':
        formula_class = Prev
    elif op == 'Once':
        formula_class = Once
    elif op == 'Eventually':
        formula_class = Eventually
    else:
        formula_class = Next
    formula = formula_class(interval, subformula)

    return formula, fv

def generate_exists(generator, size, lb, ub):
    """
    Generate an Exists formula
    Exists y. formula

    Args:
        generator (FormulaGenerator): Generator object
        size (int): remaining size of the formula
        lb (set): Lower bound of free variables
        ub (set): Upper bound of free variables
    Returns:
        Operator object: Exists object
    """
    generator.y_counter += 1
    var = Var(f"y{generator.y_counter}")
    lb = lb.copy()
    ub = ub.copy()
    lb.add(var)
    ub.add(var)
    subformula, fv = generator.generate(size - 1, fv_lb=lb, fv_ub=ub)
    formula = Exists(var, subformula)
    fv.discard(var)
    return formula, fv


def generate_and_with_relation(generator, size, lb, ub):
    """
    Generate a formula of the form alpha ∧ t1 R t2
    """
    new_size = size - 1
    if ub == set():
        subformula1, fv1 = generator.generate(new_size//2, fv_lb=lb, fv_ub=ub)
        subformula2, fv2 = generator.generate(new_size//2, fv_lb=lb, fv_ub=ub)
        formula = And(subformula1, subformula2)
        return formula, fv1.union(fv2)
    if lb == set():
        lb.add(generator.random_var(lb=ub)[0])
    alpha_formula, fv_alpha = generator.generate(new_size, fv_lb = lb, fv_ub=ub)
    if len(fv_alpha) < 2:
        t1 = generator.random_var(lb=fv_alpha, ub=ub)[0]
        t2 = generator.random_const()
    else:
        t1, t2 = generator.random_var(2, lb = fv_alpha, ub = fv_alpha)
    term_set = {x for x in [t1, t2] if x.__class__.__name__ == 'Var'}
    if not term_set.issubset(fv_alpha):
        relation = 'Equal'
    else:
        relation = generator.rng.choice(['Equal', 'Less', 'LessEq'])
    if relation == 'Equal':
        relation_formula = Equal(t1, t2)
    elif relation == 'Less':
        relation_formula = Less(t1, t2)
    else:
        relation_formula = LessEq(t1, t2)
    formula = And(alpha_formula, relation_formula)
    return formula, fv_alpha

def generate_and_with_equality(generator, size, lb, ub):
    """
    Generate a formula of the form alpha ∧ x = t
    """
    new_size = size - 1
    if ub == set():
        subformula1, fv1 = generator.generate(new_size//2, fv_lb=lb, fv_ub=ub)
        subformula2, fv2 = generator.generate(new_size//2, fv_lb=lb, fv_ub=ub)
        formula = And(subformula1, subformula2)
        return formula, fv1.union(fv2)
    if lb == set():
        lb.add(generator.random_var(lb=ub)[0])
    alpha_formula, fv_alpha = generator.generate(new_size, fv_lb = lb, fv_ub=ub)

    t = generator.random_var(lb = fv_alpha, ub = fv_alpha)[0]
    x = generator.random_const()
    equality_formula = Equal(x, t)
    formula = And(alpha_formula, equality_formula)
    return formula, fv_alpha.union({t if t.__class__.__name__ == 'Var' else None})

def generate_aggregation(generator, size, lb, ub):
    """
    Generate an aggregation formula of the form:
    Ω(var GROUP BY group_vars WHERE formula)
    """
    y_var = generator.random_var(n=1, lb=lb, ub = ub)[0]

    potential_z = ub-{y_var}
    if len(potential_z) == 0:
        generator.z_counter += 1
        z_var = Var(f"a{generator.z_counter}")
    else:
        z_var = generator.random_var(n=1, lb=potential_z, ub=potential_z)[0]
    n_gv = generator.rng.randint(len(lb-{y_var}), len(ub-{y_var}))
    group_vars = set(generator.random_var(n=n_gv, lb = lb-{y_var}, ub=ub-{y_var}))

    subformula_lb = group_vars.union({z_var})-{y_var}
    subformula_ub = ub.union(subformula_lb.copy())-{y_var}

    subformula, _ = generator.generate(size - 1, fv_lb=subformula_lb.copy(), fv_ub=subformula_ub.copy())
    op = ['CNT', 'SUM']
    if len(group_vars) > 0:
        op.extend(['MIN', 'MAX'])
    agg_operator = generator.rng.choice(op)# 'MED', 'AVG' not supported for integers

    formula = Aggreg(agg_operator, y_var, z_var, sorted(group_vars, key=lambda x: x.name), subformula)
    returning_vars = group_vars.union({y_var})
    if len(ub) == 0:
        formula = Exists(y_var, formula)
        returning_vars.remove(y_var)
    return formula, returning_vars

def generate_let(generator, size, lb, ub):
    """
    Generate a let formula of the form:
    LET var = formula IN formula
    """
    available_preds = [p for p in generator.sig.predicates if p.len >= max(len(lb),1)]
    if generator.required_pred != set():
        available_preds = [p for p in generator.sig.predicates if p in generator.required_pred]
        rnd_pred = generator.rng.choice(available_preds)
        generator.required_pred.remove(rnd_pred)
    elif available_preds == []:
        available_preds = [p for p in generator.sig.predicates if p.len >=1]
        rnd_pred = generator.rng.choice(available_preds if available_preds != [] else generator.sig.predicates)
    else:
        rnd_pred = generator.rng.choice(available_preds)

    vars_in_pred = set([Var(f"z{i}") for i in range(generator.let_counter, generator.let_counter+rnd_pred.len)])
    generator.let_counter += rnd_pred.len
    pred = Pred(rnd_pred.name, sorted(vars_in_pred, key=lambda x: x.name))

    formula1, _ = generator.generate((size-1)//2, fv_lb=vars_in_pred, fv_ub=vars_in_pred)

    generator.required_pred.add(rnd_pred)

    formula2, fv2 = generator.generate((size-1)//2, fv_lb=lb, fv_ub=ub)

    return Let(pred, vars_in_pred, formula1, formula2), fv2




### Functions for converting formulas to strings

def check_interval(interval):
    """Return string from tuple"""
    if interval[1] is None:
        return f"[{interval[0]},*)"
    else:
        return f"[{interval[0]},{interval[1]}]"

def form2str(par, h):
    """Convert formula to string"""
    if par:
        return f"({form2str(False, h)})"

    # Predicate case
    if isinstance(h, Pred):
        return h.__2str__()

    elif isinstance(h, Var):
        return h.__2str__()

    elif isinstance(h, str):
        return h

    # Equal case
    elif isinstance(h, Equal):
        return f"{form2str(False, h.var1)} = {form2str(False, h.var2)}"

    # Less case
    elif isinstance(h, Less):
        return f"{form2str(False, h.var1)} < {form2str(False, h.var2)}"

    # LessEq case
    elif isinstance(h, LessEq):
        return f"{form2str(False, h.var1)} <= {form2str(False, h.var2)}"

    # Negation case
    elif isinstance(h, Neg):
        return f"NOT {form2str(True, h.operator)}"

    # Exists case
    elif isinstance(h, Exists):
        return f"(EXISTS {h.var.__2str__()}. {form2str(True, h.operator)})"

    # ForAll case
    elif isinstance(h, ForAll):
        return f"FORALL {h.var.__2str__()}. {form2str(True, h.operator)}"

    # Prev case
    elif isinstance(h, Prev):
        return f"PREVIOUS{check_interval(h.interval)} {form2str(True, h.operator)}"

    # Once case
    elif isinstance(h, Once):
        return f"ONCE{check_interval(h.interval)} {form2str(True, h.operator)}"
    
    # Next case
    elif isinstance(h, Next):
        return f"NEXT{check_interval(h.interval)} {form2str(True, h.operator)}"
    
    # Eventually case
    elif isinstance(h, Eventually):
        return f"EVENTUALLY{check_interval(h.interval)} {form2str(True, h.operator)}"

    # And case
    elif isinstance(h, And):
        return f"{form2str(False, h.operator1)} AND {form2str(True, h.operator2)}"

    # Or case
    elif isinstance(h, Or):
        return f"({form2str(False, h.operator1)} OR {form2str(True, h.operator2)})"

    # Implies case
    elif isinstance(h, Implies):
        return f"{form2str(False, h.operator1)} IMPLIES {form2str(True, h.operator2)}"

    # Since case
    elif isinstance(h, Since):
        return f"{form2str(False, h.operator1)} SINCE{check_interval(h.interval)} {form2str(True, h.operator2)}"

    # Until case
    elif isinstance(h, Until):
        return f"{form2str(False, h.operator1)} UNTIL{check_interval(h.interval)} {form2str(True, h.operator2)}"

    elif isinstance(h, Aggreg):
        if isinstance(h.group_vars, Var):
            group_vars_str = h.group_vars.name
        else:
            group_vars_str = ", ".join([v.name for v in h.group_vars])
        return f"({h.y.name} <- {h.operator} {h.z.name}; {group_vars_str} {form2str(True, h.formula)})"

    elif isinstance(h, Let):
        return f"LET {h.predicate.__2str__()} = {form2str(True, h.operator1)}\nIN {form2str(True, h.operator2)}"

    # Error case
    else:
        raise ValueError(f"Unsupported formula type: {type(h).__name__, h}")
