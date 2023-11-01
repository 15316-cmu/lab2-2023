from __future__ import annotations
from dataclasses import dataclass
from enum import Enum

import itertools


class Operator(Enum):
    NOT = 1
    AND = 2
    OR = 3
    IMPLIES = 4
    TRUE = 5
    FALSE = 6
    SAYS = 7
    ISKEY = 8
    SIGN = 9
    ISCA = 10
    OPEN = 11
    OTHER = 12


@dataclass(eq=True, frozen=True)
class Variable():
    id: str


@dataclass(eq=True, frozen=True)
class Agent():
    id: str


@dataclass(eq=True, frozen=True)
class Key():
    fingerprint: str


@dataclass(eq=True, frozen=True)
class Resource():
    id: str


@dataclass(eq=True, frozen=True)
class App():
    op: Operator
    arity: int
    args: list[Formula]

    def __hash__(self):
        return hash((self.op, self.arity) + tuple(self.args))


@dataclass(eq=True, frozen=True)
class Forall():
    x: Variable
    p: Formula


Formula = Variable | App | Forall
Substitution = dict[Variable, Formula]


@dataclass(eq=True, frozen=True)
class Proposition():
    p: Formula


@dataclass(eq=True, frozen=True)
class Affirmation():
    a: Agent | Variable
    p: Formula


Judgement = Proposition | Affirmation


@dataclass(eq=True, frozen=True)
class Sequent:
    gamma: list[Judgement]
    delta: Judgement

    def __hash__(self):
        return hash((self.delta,) + tuple(self.gamma))


@dataclass(eq=True, frozen=True)
class Rule:
    premises: list[Sequent]
    conclusion: Sequent
    name: str


@dataclass(eq=True, frozen=True)
class Proof:
    premises: list[Proof | Sequent]
    conclusion: Sequent
    rule: Rule

    def __hash__(self):
        return hash(tuple(self.premises) + (self.conclusion,) + (self.rule.name,))

def apply_formula(p: Formula, rho: Substitution) -> Formula:
    """
    Apply a substitution to a formula
    
    Args:
        p (Formula): The formula
        rho (Substitution): The substitution
    
    Returns:
        Formula: A new formula with variables appearing in the substitution
            replaced with the corresponding formula
    """
    match p:
        case Variable(_):
            return rho[p] if p in rho else p
        case App(o, n, args):
            match o:
                case Operator.OTHER:
                    return apply_formula(args[0], rho)
                case _:
                    return App(o, n, [apply_formula(a, rho) for a in args])
        case Forall(x, p):
            return Forall(x, apply_formula(p, {v: q for v, q in rho.items() if v != x}))
    return p

def apply_judgement(j: Judgement, rho: Substitution) -> Judgement:
    """
    `apply_formula` lifted to judgements
    
    Args:
        j (Judgement): The judgement
        rho (Substitution): The substitution
    
    Returns:
        Judgement: The judgement, with `apply_formula` called on its
            enclosed formula
    """
    match j:
        case Proposition(p):
            return Proposition(apply_formula(p, rho))
        case Affirmation(a, p):
            a = a if a not in rho else rho[a]
            return Affirmation(a, apply_formula(p, rho))

def apply_sequent(seq: Sequent, rho: Substitution) -> Sequent:
    """
    `apply_judgement` lifted to sequents
    
    Args:
        seq (Sequent): The sequent
        rho (Substitution): The substitution
    
    Returns:
        Sequent: The sequent, with `apply_judgement` called on each
            judgement appearing on the left and right
    """
    gamma = [apply_judgement(p, rho) for p in seq.gamma]
    delta = apply_judgement(seq.delta, rho)
    return Sequent(gamma, delta)

def matchs(
    eqs: list[tuple[Formula, Formula]],
    rho: Substitution
) -> Optional[Substitution]:
    """
    Given a list of equations t1 = o1, ..., tn = on, find a substitution
    rho such that rho(t1) = o1, ..., rho(tn) = on.

    This implementation is extended from what was covered in lecture in two
    ways. First, quantified formulas are supported. Second, "template" holes
    like those appearing in the "forall left" rule are supported. So,
    if t1 is "F(x)" and tn is "F(e)", then `matchs` will attempt to unify
    `e` with `rho(x)`.
    
    Args:
        eqs (list[tuple[Formula, Formula]]): List of term equations to unify.
        rho (Substitution): Substitution to unify over.

    Returns:
        Optional[Substitution]: The unifying substitution described in the summary
            if one exists, otherwise `None`.
    """
    if len(eqs) == 0 or rho is None:
        return rho
    match eqs[0]:
        case Variable(x), o:
            if Variable(x) in rho:
                return matchs(eqs[1:], rho) if rho[Variable(x)] == o else None
            else:
                return matchs(eqs[1:], {**rho, Variable(x): o})
        case App(Operator.OTHER, n, a), o:
            pl_p = Variable(f'@P{a[0].id}')
            if pl_p in rho:
                if a[1] in rho:
                    rho_p = {**rho, rho[pl_p]: rho[a[1]]}
                else:
                    rho_p = {**rho, a[1]: rho[pl_p]}
                rho_p = matchs([(rho[a[0]], o)], rho_p)
                if rho_p is not None:
                    pl_v = rho_p[rho[pl_p]]
                    rho = {v: q for v, q in rho_p.items() if v not in [rho[pl_p], a[1]]}
                    return matchs(eqs[1:], {**rho, a[1]: pl_v})
                else:
                    return None
            else:
                rho = matchs(eqs[1:], {**rho, a[0]: o, pl_p: a[1]})
                return rho
        case App(o1, n1, a1), App(o2, n2, a2):
            if o1 == o2 and n1 == n2:
                return matchs(list(zip(a1,a2))+eqs[1:], rho)
        case Forall(x1, p1), Forall(x2, p2):
            old_rho = rho
            rho_x = {v: q for v, q in rho.items() if v != x1}
            rho = matchs([(p1, apply_formula(p2, {x2: x1}))] + eqs[1:], rho_x)
            rho = {**rho, x1: old_rho[x1]} if x1 in old_rho else rho
            if rho is not None:
                return {v: q for v, q in rho.items() if x1 != v}
        case o1, o2:
            return matchs(eqs[1:], rho) if o1 == o2 else None
    return None

def matchs_judgement(
    eqs: list[tuple[Judgement, Judgement]],
    rho: Substitution
) -> Optional[Substitution]:
    """
    Lifts `matchs` to judgements.
    
    Args:
        eqs (list[tuple[Judgement, Judgement]]): List of term equations over
            `Judgement` objects.
        rho (Substitution): Substitution to unify under.

    Returns:
        Optional[Substitution]: The unifying substitution described in the summary
            if one exists, otherwise `None`.
    """
    if len(eqs) == 0 or rho is None:
        return rho
    fmla_eqs = []
    for eq in eqs:
        match eq:
            case Proposition(p), Proposition(q):
                fmla_eqs.append((p, q))
            case Affirmation(Variable(x), p), Affirmation(a, q):
                rho |= {Variable(x): a}
                fmla_eqs.append((p, q))
            case Affirmation(Agent(a), p), Affirmation(Agent(b), q) if a == b:
                fmla_eqs.append((p, q))
            case _:
                return None
    return matchs(fmla_eqs, rho)

def matchs_sequent(
    seq1: Sequent,
    seq2: Sequent,
    rho: Substitution
) -> Generator[Substitution, None, None]:
    """
    Lifts `matchs_judgement` to sequents. Unlike the other `matchs`
    functions, this only attempts to unify a single pair of sequents.
    
    Args:
        seq1 (Sequent): "template" sequent
        seq2 (Sequent): Sequent to unify with the "template"
        rho (Substitution): Substitution to unify under.

    Returns:
        Generator[Substitution, None, None]: A lazily-constructed sequence
            of substitutions that unify `seq1` and `seq2`. Note that there
            may be more than one way to unify the sequents, as there are
            potentially many ways to associate judgements on the right of 
            `seq1` with those on the right of `seq2`.
    """
    if rho is not None:
        if apply_sequent(seq1, rho) == seq2:
            yield rho
        rho = matchs_judgement([(seq1.delta, seq2.delta)], rho)
        if len(seq1.gamma) == 0 and rho is not None:
            yield rho
        elif len(seq1.gamma) <= len(seq2.gamma):
            gamma_x = itertools.combinations(seq1.gamma, len(seq1.gamma))
            gamma_t = itertools.permutations(seq2.gamma, len(seq1.gamma))
            for eq in itertools.product(gamma_x, gamma_t):
                rho_c = matchs_judgement(list(zip(*eq)), rho)
                if rho_c is not None:
                    yield rho_c