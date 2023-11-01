from __future__ import annotations
import itertools

from logic import *
from parser import parse

def allvars(p: Formula|Judgement|Sequent|Proof) -> set[Variable]:
    """
    Get the set of variables appearing in a `logic` object,
    i.e., a formula, judgement, sequent, or proof.
    
    Args:
        p (Formula | Judgement | Sequent | Proof): Object to
            scan for variables.
    
    Returns:
        set[Variable]: All variables appearing in the object.
    """
    match p:
        case Variable(_):
            return set([p])
        case App(_, _, args):
            return set().union(*[allvars(arg) for arg in args])
        case Forall(x, p):
            return allvars(p) - set([x])
        case Proposition(q):
            return allvars(q)
        case Affirmation(Variable(x), q):
            return set([Variable(x)]).union(allvars(q))
        case Affirmation(Agent(_), q):
            return allvars(q)
        case Sequent(gamma, delta):
            return allvars(delta).union(*[allvars(q) for q in gamma])
        case Proof(prems, conc, _):
            return allvars(conc).union(*[allvars(prem) for prem in prems])
    return set()

def allkeys(p: Formula|Judgement|Sequent|Proof) -> set[Key|Variable]:
    """
    Get the set of keys appearing in a `logic` object. This set may 
    contain some `Variable` objects, if they appear as arguments in the
    appropriate location within `sign` and `iskey` formulas.
    
    Args:
        p (Formula | Judgement | Sequent | Proof): Object to scan for
            keys.
    
    Returns:
        set[Key | Variable]: Set described in the summary.
    """
    match p:
        case Key(_):
            return set([p])
        case App(Operator.ISKEY, _, args):
            return set([args[1]])
        case App(Operator.SIGN, _, args):
            return set([args[1]]).union(allkeys(args[0]))
        case App(_, _, args):
            return set().union(*[allkeys(arg) for arg in args])
        case Forall(_, p):
            return allkeys(p)
        case Proposition(q):
            return allkeys(q)
        case Affirmation(_, q):
            return allkeys(q)
        case Sequent(gamma, delta):
            return allkeys(delta).union(*[allkeys(q) for q in gamma])
        case Proof(prems, conc, _):
            return allkeys(conc).union(*[allkeys(prem) for prem in prems])
    return set()

def agents(p: Formula|Judgement|Sequent|Proof) -> set[Agent|Variable]:
    """
    Get the set of agents appearing in a `logic` object. This set may
    contain some `Variable` objects, if they appear as arguments in the
    appropriate location within `iskey`, `says`, `sign`, and `open` formulas.
    
    Args:
        p (Formula | Judgement | Sequent | Proof): Object to scan for
            agents.
    
    Returns:
        set[Agent | Variable]: Set described in the summary.
    """
    match p:
        case Agent(_):
            return set([p])
        case App(Operator.ISKEY, _, args):
            return set([args[0]])
        case App(Operator.SAYS, _, args):
            return set([args[0]]).union(agents(args[1]))
        case App(Operator.SIGN, _, args):
            return agents(args[0])
        case App(Operator.OPEN, _, args):
            return set([args[0]])
        case App(_, _, args):
            return set().union(*[agents(arg) for arg in args])
        case Forall(_, p):
            return agents(p)
        case Proposition(q):
            return agents(q)
        case Affirmation(a, q):
            return set([a]).union(agents(q))
        case Sequent(gamma, delta):
            return agents(delta).union(*[agents(q) for q in gamma])
        case Proof(prems, conc, _):
            return agents(conc).union(*[agents(prem) for prem in prems])
    return set()

def resources(p: Formula|Judgement|Sequent|Proof) -> set[Resource|Variable]:
    """
    Get the set of resources appearing in a `logic` object. This set may
    contain some `Variable` objects, if they appear as arguments in the
    appropriate location within `says`, `open`, and `sign` formulas.
    
    Args:
        p (Formula | Judgement | Sequent | Proof): Object to scan for resources.
    
    Returns:
        set[Resource | Variable]: Set described in the summary.
    """
    match p:
        case Resource(_):
            return set([p])
        case App(Operator.SAYS, _, args):
            return resources(args[1])
        case App(Operator.OPEN, _, args):
            return set([args[1]])
        case App(Operator.SIGN, _, args):
            return resources(args[0])
        case App(_, _, args):
            return set().union(*[resources(arg) for arg in args])
        case Forall(_, p):
            return resources(p)
        case Proposition(q):
            return resources(q)
        case Affirmation(a, q):
            return resources(q)
        case Sequent(gamma, delta):
            return resources(delta).union(*[resources(q) for q in gamma])
        case Proof(prems, conc, _):
            return resources(conc).union(*[resources(prem) for prem in prems])
    return set()

def fresh_var(p: Formula|Judgement|Sequent|Proof, prefix='v') -> Variable:
    """
    Generate a fresh variable that does not appear anywhere in the syntax of
    a `logic` object. The variable will be given a specified prefix, with an
    integer suffix depending on the variables in the given `logic` object.
    
    Args:
        p (Formula | Judgement | Sequent | Proof): Object to scan for
            existing variables.
        prefix (str, optional): Prefix to give the returned variable. Defaults
            to "v".
    
    Returns:
        Variable: Fresh variable described in the summary.
    """
    vs = allvars(p)
    i = 0
    while Variable(f'{prefix}{i}') in vs:
        i += 1
    return Variable(f'{prefix}{i}')

def is_ca_key(k: Key, seq: Sequent, ca: Optional[Agent]=None) -> bool:
    """
    Check whether a given key belongs to a certificate authority,
    as determined by the assumptions in the context of a given sequent.
    
    Args:
        k (Key): The key to check.
        seq (Sequent): The sequent to scan.
        ca (Agent, optional): If given, check whether the
            specified key belongs to a particular CA.
    
    Returns:
        bool: `True` if the context of `seq` contains `iskey(A, k)` for some
            agent `A` for which the context also contains `ca(A)`.
    """
def is_ca_key(k: Key, seq: Sequent, ca: Optional[Agent]=None):
    for p in seq.gamma:
        match p:
            case Proposition(App(Operator.ISKEY, _, [ag, pk])):
                if ca is None:
                    return Proposition(App(Operator.ISCA, 1, [ag])) in seq.gamma
                elif ag == ca and pk == k:
                    return True

    return False

def get_cas(seq: Sequent) -> set[Agent]:
    """
    Get the set of agents listed as certificate authorities in the context of
    a given sequent.
    
    Args:
        seq (Sequent): The sequent to scan.
    
    Returns:
        set[Agent]: The set described in the summary.
    """
    cas = set([])
    for p in seq.gamma:
        match p:
            case Proposition(App(Operator.ISCA, _, [ag])):
                cas |= set([ag])
    return cas

def get_ca_key(seq: Sequent, ca: Optional[Agent]=None) -> set[Key]:
    """
    Get a set of keys belonging to certificate authorities, depending on
    the context of a given sequent. If an optional specific CA is given,
    then only return the keys belonging to that CA.
    
    Args:
        seq (Sequent): The sequent to scan.
        ca (Optional[Agent], optional): If specified, a CA to focus on.
    
    Returns:
        set[Key]: The set described in the summary.
    """
    ca_keys = set([])
    ks = allkeys(seq)
    for k in ks:
        if is_ca_key(k, seq, ca=ca):
            ca_keys |= set([k])
    return ca_keys

def is_key(k: Key, a: Agent, seq: Sequent) -> bool:
    """
    Check whether a given key belongs to a given agent, depending on the
    context of a given sequent. This check will look both for certificates
    signed by a CA in the context of `seq`, as well as `iskey` assumptions
    that are already in the context.
    
    Args:
        k (Key): Key to check.
        a (Agent): Agent to check.
        seq (Sequent): Sequent to scan.
    
    Returns:
        bool: `True` if there is either a certificate or `iskey` formula in the
            context of `seq` that associates agent `a` with `k`. `False` otherwise.
    """
    for p in seq.gamma:
        match p:
            case Proposition(App(Operator.SIGN, _, [App(Operator.ISKEY, _, [ag, pk]), ca_k])):
                if ag == a and pk == k and is_ca_key(ca_k, seq):
                    return True
            case Proposition(App(Operator.ISKEY, _, [ag, pk])):
                if ag == a and pk == k:
                    return True
    return False

def is_credential(cred: Formula, a: Agent, p: Formula, seq: Sequent) -> bool:
    """
    Check whether a formula is a credential signed by a given agent, depending
    on the context of a given sequent.
    
    Args:
        cred (Formula): Credential in question.
        a (Agent): Agent to check.
        p (Formula): Formula to check.
        seq (Sequent): Sequent to scan.
    
    Returns:
        bool: `True` if `cred` is `sign(p, [k])` and `seq` has a formula
            establishing that `k` belongs to `a`. `False` otherwise.
    """
    match cred:
        case App(Operator.SIGN, _, [q, k]) if q == p:
            return is_key(k, a, seq)
    return False

def has_credential(a: Agent, p: Formula, seq: Sequent) -> Optional[Formula]:
    """
    Check whether the context of a given sequent contains a credential for a given
    formula signed by a given agent.
    
    Args:
        a (Agent): Agent issuing the credential.
        p (Formula): Formula in the credential.
        seq (Sequent): Sequent to scan.
    
    Returns:
        Optional[Formula]: If such a credential exists, i.e. if `seq.gamma` contains
            `sign(p, [k])` for a key `k` belonging to `a`, then it is returned.
            Otherwise `None`.
    """
    for q in seq.gamma:
        if is_credential(q.p, a, p, seq):
            return q
    return None


def fmla_stringify(p: Formula) -> str:
    op_dict = {
        Operator.NOT: '!',
        Operator.AND: '&',
        Operator.OR: '|',
        Operator.IMPLIES: '->',
        Operator.SAYS: 'says',
        Operator.ISCA: 'ca'
    }
    match p:
        case Variable(id)|Resource(id)|Agent(id)|Key(id):
            return f"{id}"
        case App(op, arity, args):
            if arity == 0:
                return f"{'true' if op == Operator.TRUE else 'false'}"
            if arity == 1:
                return f"{op_dict[op]}({fmla_stringify(args[0])})"
            else:
                match op:
                    case Operator.SIGN:
                        return f"sign(({fmla_stringify(args[0])}), {fmla_stringify(args[1])})"
                    case Operator.ISKEY:
                        return f"iskey({fmla_stringify(args[0])}, {fmla_stringify(args[1])})"
                    case Operator.OPEN:
                        return f"open({fmla_stringify(args[0])}, {fmla_stringify(args[1])})"
                    case Operator.OTHER:
                        return f"{fmla_stringify(args[0])}({fmla_stringify(args[1])})"
                return "(" + f" {op_dict[op]} ".join([fmla_stringify(q) for q in args]) + ")"
        case Forall(x, p):
            return f"(@{fmla_stringify(x)} . ({fmla_stringify(p)}))"
        case _:
            raise TypeError(
                f"fmla_stringify got {type(p)} ({p}), not Formula"
            )
            
def judgement_stringify(j: Judgement) -> str:
    match j:
        case Proposition(p):
            return f'{fmla_stringify(p)} true'
        case Affirmation(a, p):
            return f'{a.id} aff {fmla_stringify(p)}'
        case _:
            raise TypeError(
                f'judgement_stringify got {type(j)} ({j}), not Judgement'
            )

def sequent_stringify(seq: Sequent, max_line: int=None, include_gamma=False, trunc_context=False) -> str:
    gamma = [judgement_stringify(p) for p in seq.gamma]
    delta = [judgement_stringify(seq.delta)]
    
    total_len = sum([len(p) for p in gamma]) + sum([len(q) for q in delta]) + 3
    gammas = "Gamma, " if len(gamma) > 0 else "Gamma"
    gammas = gammas if include_gamma else ""
    
    if max_line is None or total_len < max_line or trunc_context:
        return f"{gammas}{', '.join(gamma) if not trunc_context else '...'} |- {', '.join(delta)}"
    else:
        width = max([len(gamma) for gamma in gammas] + [''])
        nl_gammas = [f"{{:>{width}s}},\n".format(g) for g in gamma[:-1]] + [gamma[-1]]
        nl_deltas = [f"{d},\n" for d in delta[:-1]] + [delta[-1]]
        return f"{gammas}{''.join(nl_gammas)} \n    |-  {'    '.join(nl_deltas)}"
    
def rule_stringify(rule: Rule) -> str:
    premises = [sequent_stringify(seq, include_gamma=True) for seq in rule.premises]
    conclusion = sequent_stringify(rule.conclusion, include_gamma=True)
    newline = "\n"
    premise_break = newline if len(premises) > 0 else ""
    return f"{newline.join(premises)}{premise_break}{'-'*max([len(s) for s in premises + [conclusion]])}\n{conclusion}"
    
def subst_stringify(rho: Substitution) -> str:
    subs = []
    for lit in rho.keys():
        subs.append(f"{fmla_stringify(lit)} => {fmla_stringify(rho[lit])}")
    return ", ".join(subs)

def max_width(s: str) -> int:
    return max([len(line.replace('\t', ' '*8)) for line in s.split('\n')])

def horizontal_concat(ss: list[str], lead=0, sep_width=2) -> str:
    max_lines = max([len(s.split('\n')) for s in ss])
    newline = '\n'
    ss = [f'{newline*(max_lines-len(s.split(newline)))}{s}' for s in ss]
    lines = itertools.zip_longest(*[s.split('\n') for s in ss])
    catteds = []
    widths = [max_width(s) for s in ss]
    linespecs = [f'{{:^{width}s}}' for width in widths]
    leadstr = ' '*lead
    for line in lines:
        catted = f'{" "*sep_width}'.join(
            [linespecs[i].format(s if s is not None else ' ') for i, s in enumerate(line)]
        )
        catted = f'{catted}'
        catteds.append(catted)
    return '\n'.join(catteds)

def ps_helper(
    pf: Proof,
    lead=0,
    sep_width=2,
    pf_width=80,
    sub_index='T',
    overflow={},
    trunc_context=False,
    depth=None
) -> str:

    if depth is not None and depth <= 0:
        return "...", {}
    else:
        if depth is not None:
            depth -= 1

    if isinstance(pf, Sequent):
        return sequent_stringify(pf, max_line=pf_width, trunc_context=trunc_context), {}

    rule_width = len(pf.rule.name)+2

    if len(pf.premises) > 0:
        root = sequent_stringify(pf.conclusion, max_line=pf_width, trunc_context=trunc_context)
        subs = [
            ps_helper(
                p,
                lead=lead,
                pf_width=pf_width,
                sub_index=f'{sub_index}.{i}',
                overflow=overflow,
                trunc_context=trunc_context,
                depth=depth
            ) for i, p in enumerate(pf.premises)
        ]
        for sub in subs:
            overflow |= sub[1]
        branches = [sub[0] for sub in subs]
        cat_branches = horizontal_concat(branches, lead=rule_width-1, sep_width=sep_width)
        if max_width(cat_branches) >= pf_width and len(branches) > 1:
            leadstr = ' '*(rule_width-2)
            root = f'{leadstr}{root}'
            overflow |= {f'{sub_index}.{i}': branch for i, branch in enumerate(branches)}
            branches = [f'{sub_index}.{i}' for i, _ in enumerate(branches)]
            leadstr = ' '*(rule_width)
            branches = (' '*sep_width).join(branches)
            width = max(max_width(branches), max_width(root))+rule_width
            branches = f'{leadstr}{branches}'
        else:
            branches = cat_branches
    else:
        root = f'{" "*(rule_width-2)}{sequent_stringify(pf.conclusion, max_line=pf_width, trunc_context=trunc_context)}'
        branches = f'{" "*(rule_width-2)}*'
    width = max(max_width(branches), max_width(root))+rule_width+2
    main_proof = f'{branches}\n{pf.rule.name} {"-"*(width-rule_width)}\n{{:^{width}}}'.format(root)
    return main_proof, overflow


def proof_stringify(pf: Proof, sep_width=2, pf_width=80, trunc_context=False, depth=None) -> str:
    s, overflow = ps_helper(
        pf,
        lead=0,
        sep_width=sep_width,
        pf_width=pf_width,
        sub_index='T',
        trunc_context=trunc_context,
        depth=depth
    )
    if len(overflow) > 0:
        extras = '\n\n'.join(f'Proof {k}:\n{horizontal_concat([overflow[k]])}' for k in reversed(overflow))
        return f'{horizontal_concat([s])}\n\n{extras}'
    else:
        return horizontal_concat([s])


def stringify(o, pf_width=80, seq_width=None, trunc_context=False, pf_depth=None) -> str:
    if isinstance(o, Formula):
        return fmla_stringify(o)
    elif isinstance(o, Judgement):
        return judgement_stringify(o)
    elif isinstance(o, Sequent):
        return sequent_stringify(o, max_line=seq_width, trunc_context=trunc_context)
    elif isinstance(o, dict):
        return subst_stringify(o)
    elif isinstance(o, Rule):
        return rule_stringify(o)
    elif isinstance(o, Proof):
        return proof_stringify(o, pf_width=pf_width, trunc_context=trunc_context, depth=pf_depth)
    else:
        return fmla_stringify(o)
