from __future__ import annotations
from functools import cache
import itertools

from logic import *
from parser import parse
from util import allvars, stringify
from proofrules import (
    identityRule,
    falseLeftRule,
    impRightRule,
    impLeftRule,
    weakenRule,
    affRule,
    saysLeftRule,
    saysRightRule,
    signRule,
    certRule,
    calculus
)

def print_feedback(pf: Proof, message: str):
    print('*'*20, 'Illegal proof step', '*'*20)
    print(stringify(pf, pf_depth=2, pf_width=80))
    print('*'*60)
    print(message)

def verify_identity(pf: Proof, feedback: bool=True) -> bool:

    if len(pf.premises) > 0:
        if feedback:
            print_feedback(pf, f'id rule has no premises, {len(pf.premises)} are given')
        return False
    if not isinstance(pf.conclusion.delta, Proposition):
        if feedback:
            print_feedback(pf, f'id rule must have a Proposition judgement as goal')
        return False
    if not pf.conclusion.delta in pf.conclusion.gamma:
        if  feedback:
            print_feedback(pf, f'Proof goal ({stringify(pf.conclusion.delta)}) not in assumptions')
        return False

    return True

def verify_botl(pf: Proof, feedback: bool=True) -> bool:

    if len(pf.premises) > 0:
        if feedback:
            print_feedback(pf, f'botL rule has no premises, {len(pf.premises)} are given')
        return False
    if not isinstance(pf.conclusion.delta, Proposition):
        if feedback:
            print_feedback(pf, f'botL rule must have a Proposition judgement as goal')
        return False
    if not Proposition(App(Operator.FALSE, 0, [])) in pf.conclusion.gamma:
        if  feedback:
            print_feedback(pf, f'Proof goal ({stringify(Proposition(App(Operator.FALSE, 0, [])))}) not in assumptions')

    return True

def verify_impright(pf: Proof, feedback: bool=True) -> bool:

    if len(pf.premises) != 1:
        if feedback:
            print_feedback(pf, f'->R rule has one premise, {len(pf.premises)} are given')
        return False
    if not isinstance(pf.conclusion.delta, Proposition):
        if feedback:
            print_feedback(pf, f'->R rule must have a Proposition judgement as goal')
        return False
    if not (isinstance(pf.conclusion.delta.p, App) and pf.conclusion.delta.p.op == Operator.IMPLIES):
        if  feedback:
            print_feedback(pf, f'->R rule expects implication goal, got {stringify(pf.conclusion.delta)}')
        return False

    ant = pf.conclusion.delta.p.args[0]
    suc = pf.conclusion.delta.p.args[1]

    gamma = pf.premises[0].gamma if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.gamma
    delta = pf.premises[0].delta if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.delta

    if not Proposition(suc) == delta:
        if feedback:
            print_feedback(pf, f'{stringify(suc)} must be the premise goal, got {stringify(delta.p)}')
        return False

    extra_assumes = set(gamma) - (set(pf.conclusion.gamma)|set([Proposition(ant)]))
    if len(extra_assumes) > 0:
        offensive_assumes = ', '.join([stringify(p) for p in extra_assumes])
        if feedback:
            print_feedback(pf, f'Illegal assumptions in premise: {offensive_assumes}')
        return False

    return True

def verify_impleft(pf: Proof, feedback: bool=True) -> bool:

    if len(set(p for p in pf.conclusion.gamma if (isinstance(p.p, App) and p.p.op == Operator.IMPLIES))) == 0:
        if feedback:
            print_feedback(pf, '->L rule needs an implication in the assumptions')
        return False
    if len(pf.premises) != 2:
        if feedback:
            print_feedback(pf, f'->L rule has two premises, {len(pf.premises)} are given')
        return False

    gamma0 = pf.premises[0].gamma if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.gamma
    delta0 = pf.premises[0].delta if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.delta
    gamma1 = pf.premises[1].gamma if isinstance(pf.premises[1], Sequent) else pf.premises[1].conclusion.gamma
    delta1 = pf.premises[1].delta if isinstance(pf.premises[1], Sequent) else pf.premises[1].conclusion.delta

    if not pf.conclusion.delta == delta1:
        if feedback:
            print_feedback(pf, f'{stringify(pf.conclusion.delta.p)} must be the right premise goal, got {stringify(delta1.p)}')
        return False

    extra_assumes = set(gamma0) - set(pf.conclusion.gamma)
    if len(extra_assumes) > 0:
        if feedback:
            offensive_assumes = ', '.join([stringify(p) for p in extra_assumes])
            print_feedback(pf, f'Illegal assumptions in left premise: {offensive_assumes}')
        return False

    extra_assumes = set(gamma1) - set(pf.conclusion.gamma)
    if len(extra_assumes) > 0:
        bad_assumes = []
        for p in extra_assumes:
            imp = App(Operator.IMPLIES, 2, [delta0.p, p.p])
            if not Proposition(imp) in pf.conclusion.gamma:
                bad_assumes.append(p.p)
        if len(bad_assumes) > 0:
            offensive_assumes = ', '.join([stringify(p) for p in bad_assumes])
            if feedback:
                print_feedback(pf, f'Illegal assumptions in right premise: {offensive_assumes}')
            return False

    return True

def verify_leftforall(pf: Proof, feedback: bool=True) -> bool:

    if len(set(p for p in pf.conclusion.gamma if isinstance(p.p, Forall))) == 0:
        if feedback:
            print_feedback(pf, '@L rule needs a quantified formula in the assumptions')
        return False
    if len(pf.premises) != 1:
        if feedback:
            print_feedback(pf, f'@L rule has only one premise, {len(pf.premises)} are given')
        return False
    
    delta = pf.premises[0].delta if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.delta
    gamma = pf.premises[0].gamma if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.gamma

    if pf.conclusion.delta != delta:
        if feedback:
            print_feedback(pf, f'Goals do not match: {stringify(pf.conclusion.delta)}, {stringify(delta)}')
        return False
    
    prems = list(set(gamma) ^ set(pf.conclusion.gamma))
    if len(prems) > 2:
        if feedback:
            fa_assumes = [p.p.p for p in pf.conclusion.gamma if isinstance(p.p, Forall)]
            offensive_assumes = ', '.join([stringify(p.p) for p in set(prems) - set(fa_assumes) - set(pf.conclusion.gamma)])
            print_feedback(pf, f'Illegal assumptions in premise, one of: {offensive_assumes}')
        return False
    eq = (prems[0].p, prems[1].p) if prems[0] in pf.conclusion.gamma else (prems[1].p, prems[0].p)
    x = eq[0].x
    rho = matchs([(eq[0].p, eq[1])], {})
    if rho is None or x not in rho:
        if feedback:
            print_feedback(pf, f'Could not unify {stringify(prems[1].p)} with {stringify(prems[0].p.p)} by substituting {x.id}')
        return False
    if apply_formula(eq[0].p, {x: rho[x]}) != eq[1]:
        if feedback:
            print_feedback(pf, f'Could not unify {stringify(prems[1].p)} with {stringify(prems[0].p.p)} by substituting {x.id}')
        return False

    sub_gamma = set(Proposition(apply_formula(p.p.p, {x: rho[x]})) for p in pf.conclusion.gamma if isinstance(p.p, Forall))
    if len(sub_gamma & set(gamma)) == 0:
        if feedback:
            needed_assumes = ', '.join(stringify(p.p) for p in sub_gamma)
            print_feedback(pf, f'Expected to find one of the following assumptions in premise: {needed_assumes}')

    return True

def verify_rightforall(pf: Proof, feedback: bool=True) -> bool:

    if not isinstance(pf.conclusion.delta, Proposition):
        if feedback:
            print_feedback(pf, '@R rule requires proposition judgement')
        return False
    if not isinstance(pf.conclusion.delta.p, Forall):
        if feedback:
            print_feedback(pf, '@R rule needs quantified formula as goal')
        return False
    if len(pf.premises) != 1:
        if feedback:
            print_feedback(pf, f'@R rule has only one premise, {len(pf.premises)} are given')
        return False

    delta = pf.premises[0].delta if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.delta

    v = pf.conclusion.delta.p.x
    rho = matchs([(pf.conclusion.delta.p.p, delta.p)], {})
    if rho is None or v not in rho.keys():
        if feedback:
            print_feedback(pf, f'Could not unify {stringify(delta.p)} with {stringify(pf.conclusion.delta.p.p)}')
        return False
    if not apply_formula(pf.conclusion.delta.p.p, rho) == delta.p:
        if feedback:
            print_feedback(pf, f'Could not unify {stringify(delta.p)} with {stringify(pf.conclusion.delta.p.p)}')
        return False
    if rho[v] in allvars(pf.conclusion):
        if feedback:
            print_feedback(pf, f'Illegal substitution, {stringify(v)} already appears in sequent')
        return False

    return True

def verify_weaken(pf: Proof, feedback: bool=True) -> bool:

    if len(pf.premises) != 1:
        if feedback:
            print_feedback(pf, f'W rule has only one premise, {len(pf.premises)} are given')
        return False

    delta = pf.premises[0].delta if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.delta
    gamma = pf.premises[0].gamma if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.gamma

    if pf.conclusion.delta != delta:
        if feedback:
            print_feedback(pf, f'Goals do not match: {stringify(pf.conclusion.delta)}, {stringify(delta)}')
        return False
    if not set(gamma).issubset(set(pf.conclusion.gamma)):
        if feedback:
            offensive_assumes = ', '.join([stringify(p.p) for p in set(gamma) - set(pf.conclusion.gamma)])
            print_feedback(pf, f'Premise assumptions are not subset of conclusion: {offensive_assumes}')
        return False

    return True

def verify_cut(pf: Proof, feedback: bool=True) -> bool:

    if len(pf.premises) != 2:
        if feedback:
            print_feedback(pf, f'cut rule has two premises, {len(pf.premises)} are given')
        return False

    prem0_delta = pf.premises[0].delta if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.delta
    prem1_delta = pf.premises[1].delta if isinstance(pf.premises[1], Sequent) else pf.premises[1].conclusion.delta
    prem0_gamma = pf.premises[0].gamma if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.gamma
    prem1_gamma = pf.premises[1].gamma if isinstance(pf.premises[1], Sequent) else pf.premises[1].conclusion.gamma

    if pf.conclusion.delta != prem1_delta:
        if feedback:
            print_feedback(pf, f'Goals do not match: {stringify(pf.conclusion.delta)}, {stringify(prem1_delta)}')
        return False
    if len(set(prem0_gamma) - set(pf.conclusion.gamma)) > 0:
        if feedback:
            offensive_assumes = ', '.join([stringify(p.p) for p in set(prem0_gamma) - set(pf.conclusion.gamma)])
            print_feedback(pf, f'Illegal assumptions in left premise: {offensive_assumes}')
        return False
    if len(set(prem1_gamma) - (set(pf.conclusion.gamma)|set([prem0_delta]))) > 0:
        if feedback:
            offensive_assumes = ', '.join(
                [stringify(p.p) for p in set(prem1_gamma) - (set(pf.conclusion.gamma)|set([prem0_delta]))]
            )
            print_feedback(pf, f'Illegal assumptions in right premise: {offensive_assumes}')
        return False
    return True

def verify_aff(pf: Proof, feedback: bool=True) -> bool:

    if len(pf.premises) != 1:
        if feedback:
            print_feedback(pf, f'aff rule has one premise, {len(pf.premises)} are given')
        return False

    delta = pf.premises[0].delta if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.delta
    gamma = pf.premises[0].gamma if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.gamma

    if not isinstance(pf.conclusion.delta, Affirmation):
        if feedback:
            print_feedback(pf, f'conclusion must be an affirmation judgement, got {stringify(pf.conclusion.delta)}')
        return False
    if not isinstance(delta, Proposition):
        if feedback:
            print_feedback(pf, f'premise must be a truth judgement, got {stringify(delta)}')
        return False
    if not pf.conclusion.delta.p == delta.p:
        if feedback:
            print_feedback(pf, f'Premise goal does not match conclusion affirmation')
        return False
    if not set(gamma).issubset(set(pf.conclusion.gamma)):
        if feedback:
            offensive_assumes = ', '.join([stringify(p.p) for p in set(gamma) - set(pf.conclusion.gamma)])
            print_feedback(pf, f'Premise assumptions are not subset of conclusion: {offensive_assumes}')
        return False

    return True

def verify_saysleft(pf: Proof, feedback: bool=True) -> bool:

    says_assumes = set(
        p for p in pf.conclusion.gamma 
        if (isinstance(p.p, App) and p.p.op == Operator.SAYS)
    )
    if len(says_assumes) == 0:
        if feedback:
            print_feedback(pf, 'saysL rule needs a "says" formula in the assumptions')
        return False
    if len(pf.premises) != 1:
        if feedback:
            print_feedback(pf, f'saysL rule has only one premise, {len(pf.premises)} are given')
        return False
    if not isinstance(pf.conclusion.delta, Affirmation):
        if feedback:
            print_feedback(pf, 'saysL rule must be applied with affirmation in goal')
        return False

    ag = pf.conclusion.delta.a
    delta = pf.premises[0].delta if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.delta
    gamma = pf.premises[0].gamma if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.gamma

    if pf.conclusion.delta != delta:
        if feedback:
            print_feedback(pf, f'Goals do not match: {stringify(pf.conclusion.delta)}, {stringify(delta)}')
        return False

    new_assumes = set(gamma) - set(pf.conclusion.gamma)
    if len(new_assumes) > 0:
        bad_assumes = []
        for p in new_assumes:
            if not Proposition(App(Operator.SAYS, 2, [ag, p.p])) in pf.conclusion.gamma:
               bad_assumes.append(p.p)
        if len(bad_assumes) > 0:
            offensive_assumes = ', '.join([stringify(p) for p in bad_assumes])
            if feedback:
                print_feedback(pf, f'Illegal assumptions in premise: {offensive_assumes}')
            return False

    return True

def verify_saysright(pf: Proof, feedback: bool=True) -> bool:

    if not isinstance(pf.conclusion.delta, Proposition):
        if feedback:
            print_feedback(pf, f'saysR rule requires truth judgement as goal, got {stringify(pf.conclusion.delta)}')
        return False
    if not (isinstance(pf.conclusion.delta.p, App) and pf.conclusion.delta.p.op == Operator.SAYS):
        if feedback:
            print_feedback(pf, f'saysR rule requires "says" formula as goal, got {stringify(pf.conclusion.delta.p)}')
        return False
    if len(pf.premises) != 1:
        if feedback:
            print_feedback(pf, f'saysR rule has one premise, got {len(pf.premises)}')
        return False

    delta = pf.premises[0].delta if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.delta
    gamma = pf.premises[0].gamma if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.gamma

    if not isinstance(delta, Affirmation):
        if feedback:
            print_feedback(pf, f'saysR rule requires affirmation as premise goal, got {stringify(delta)}')
        return False

    says_ag = pf.conclusion.delta.p.args[0]
    aff_ag = delta.a
    says_p = pf.conclusion.delta.p.args[1]
    aff_p = delta.p

    if says_ag != aff_ag:
        if feedback:
            print_feedback(pf, f'Mismatched agents: {stringify(says_ag)} and {stringify(aff_ag)}')
        return False
    if says_p != aff_p:
        if feedback:
            print_feedback(pf, f'Mismatched statements: ({stringify(says_p)}) and ({stringify(aff_p)})')
        return False

    if not set(gamma).issubset(set(pf.conclusion.gamma)):
        if feedback:
            offensive_assumes = ', '.join([stringify(p.p) for p in set(gamma) - set(pf.conclusion.gamma)])
            print_feedback(pf, f'Premise assumptions are not subset of conclusion: {offensive_assumes}')
        return False

    return True

def verify_sign(pf: Proof, feedback: bool=True) -> bool:

    if not isinstance(pf.conclusion.delta, Proposition):
        if feedback:
            print_feedback(pf, f'Sign rule requires truth judgement as goal, got {stringify(pf.conclusion.delta)}')
        return False
    if not (isinstance(pf.conclusion.delta.p, App) and pf.conclusion.delta.p.op == Operator.SAYS):
        if feedback:
            print_feedback(pf, f'Sign rule requires "says" formula as goal, got {stringify(pf.conclusion.delta.p)}')
        return False
    if len(pf.premises) != 2:
        if feedback:
            print_feedback(pf, f'Sign rule has two premises, got {len(pf.premises)}')
        return False

    gamma0 = pf.premises[0].gamma if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.gamma
    delta0 = pf.premises[0].delta if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.delta
    gamma1 = pf.premises[1].gamma if isinstance(pf.premises[1], Sequent) else pf.premises[1].conclusion.gamma
    delta1 = pf.premises[1].delta if isinstance(pf.premises[1], Sequent) else pf.premises[1].conclusion.delta
    ag = pf.conclusion.delta.p.args[0]
    p = pf.conclusion.delta.p.args[1]

    if not isinstance(delta0, Proposition):
        if feedback:
            print_feedback(pf, f'Left premise of sign rule should be truth judgement, got {stringify(delta0)}')
        return False
    if not (isinstance(delta0.p, App) and delta0.p.op == Operator.ISKEY):
        if feedback:
            print_feedback(pf, f'Left premise of sign rule should be "iskey" formula')
        return False
    if not isinstance(delta1, Proposition):
        if feedback:
            print_feedback(pf, f'Right premise of sign rule should be truth judgement, got {stringify(delta1)}')
        return False
    if not (isinstance(delta1.p, App) and delta1.p.op == Operator.SIGN):
        if feedback:
            print_feedback(pf, f'Left premise of sign rule should be "sign" formula')
        return False

    if not ag == delta0.p.args[0]:
        if feedback:
            print_feedback(pf, f'Agents should match: {ag.id} and {delta0.p.args[0].id}')
        return False
    if not p == delta1.p.args[0]:
        if feedback:
            print_feedback(pf, f'Formulas should match: ({stringify(p)}), ({stringify(delta1.p.args[0])})')
        return False
    if not delta0.p.args[1] == delta1.p.args[1]:
        if feedback:
            print_feedback(pf, f'Keys should match: {stringify(delta0.p.args[1])} and {stringify(delta1.p.args[1])}')
        return False

    if not set(gamma0).issubset(set(pf.conclusion.gamma)):
        if feedback:
            offensive_assumes = ', '.join([stringify(p.p) for p in set(gamma0) - set(pf.conclusion.gamma)])
            print_feedback(pf, f'Left premise assumptions are not subset of conclusion: {offensive_assumes}')
        return False
    if not set(gamma1).issubset(set(pf.conclusion.gamma)):
        if feedback:
            offensive_assumes = ', '.join([stringify(p.p) for p in set(gamma1) - set(pf.conclusion.gamma)])
            print_feedback(pf, f'Right premise assumptions are not subset of conclusion: {offensive_assumes}')
        return False

    return True

def verify_cert(pf: Proof, feedback: bool=True) -> bool:

    if not isinstance(pf.conclusion.delta, Proposition):
        if feedback:
            print_feedback(pf, f'Cert rule requires truth judgement as goal, got {stringify(pf.conclusion.delta)}')
        return False
    if not (isinstance(pf.conclusion.delta.p, App) and pf.conclusion.delta.p.op == Operator.ISKEY):
        if feedback:
            print_feedback(pf, f'Cert rule requires "iskey" formula as goal, got {stringify(pf.conclusion.delta.p)}')
        return False
    if len(pf.premises) != 2:
        if feedback:
            print_feedback(pf, f'Cert rule has two premises, got {len(pf.premises)}')
        return False

    gamma0 = pf.premises[0].gamma if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.gamma
    delta0 = pf.premises[0].delta if isinstance(pf.premises[0], Sequent) else pf.premises[0].conclusion.delta
    gamma1 = pf.premises[1].gamma if isinstance(pf.premises[1], Sequent) else pf.premises[1].conclusion.gamma
    delta1 = pf.premises[1].delta if isinstance(pf.premises[1], Sequent) else pf.premises[1].conclusion.delta
    ag = pf.conclusion.delta.p.args[0]
    k = pf.conclusion.delta.p.args[1]

    if not isinstance(delta0, Proposition):
        if feedback:
            print_feedback(pf, f'Left premise of sign rule should be truth judgement, got {stringify(delta0)}')
        return False
    if not (isinstance(delta0.p, App) and delta0.p.op == Operator.ISCA):
        if feedback:
            print_feedback(pf, f'Left premise of sign rule should be "ca" formula')
        return False
    if not isinstance(delta1, Proposition):
        if feedback:
            print_feedback(pf, f'Right premise of sign rule should be truth judgement, got {stringify(delta1)}')
        return False
    if not (isinstance(delta1.p, App) and delta1.p.op == Operator.SAYS):
        if feedback:
            print_feedback(pf, f'Left premise of sign rule should be "says" formula')
        return False
    if not (isinstance(delta1.p.args[1], App) and delta1.p.args[1].op == Operator.ISKEY):
        if feedback:
            print_feedback(pf, f'Right premise of sign rule should be "... says iskey({stringify(ag)}, {stringify(k)})" formula')
        return False

    if not ag == delta1.p.args[1].args[0]:
        if feedback:
            print_feedback(pf, f'Agents should match: {ag.id} and {stringify(delta1.p.args[1].args[0])}')
        return False
    if not delta0.p.args[0] == delta1.p.args[0]:
        if feedback:
            print_feedback(pf, f'Agents should match: {stringify(delta0.p.args[0])} and {stringify(delta1.p.args[0])}')
        return False
    if not k == delta1.p.args[1].args[1]:
        if feedback:
            print_feedback(pf, f'Keys should match: ({stringify(k)}), ({stringify(delta1.p.args[1].args[1])})')
        return False

    if not set(gamma0).issubset(set(pf.conclusion.gamma)):
        if feedback:
            offensive_assumes = ', '.join([stringify(p.p) for p in set(gamma0) - set(pf.conclusion.gamma)])
            print_feedback(pf, f'Left premise assumptions are not subset of conclusion: {offensive_assumes}')
        return False
    if not set(gamma1).issubset(set(pf.conclusion.gamma)):
        if feedback:
            offensive_assumes = ', '.join([stringify(p.p) for p in set(gamma1) - set(pf.conclusion.gamma)])
            print_feedback(pf, f'Right premise assumptions are not subset of conclusion: {offensive_assumes}')
        return False

    return True

def verify_step(pf: Proof, feedback: bool=True) -> bool:
    if pf.rule.name not in calculus:
        return False
    match pf.rule.name:
        case 'id':
            return verify_identity(pf, feedback)
        case 'botL':
            return verify_botl(pf, feedback)
        case '->R':
            return verify_impright(pf, feedback)
        case '->L'|'->Laff':
            return verify_impleft(pf, feedback)
        case '@L'|'@Laff':
            return verify_leftforall(pf, feedback)
        case '@R':
            return verify_rightforall(pf, feedback)
        case 'W':
            return verify_weaken(pf, feedback)
        case 'cut'|'affcut':
            return verify_cut(pf, feedback)
        case 'aff':
            return verify_aff(pf, feedback)
        case 'saysL':
            return verify_saysleft(pf, feedback)
        case 'saysR':
            return verify_saysright(pf, feedback)
        case 'sign':
            return verify_sign(pf, feedback)
        case 'cert':
            return verify_cert(pf, feedback)
        case _:
            return False

@cache
def verify(pf: Proof, feedback: bool=True) -> list[Sequent]:
    if isinstance(pf, Sequent):
        return [pf]
    if not verify_step(pf, feedback=feedback):
        return [pf.conclusion]
    obs = [premise for premise in pf.premises if isinstance(premise, Sequent)]
    for premise in [premise for premise in pf.premises if isinstance(premise, Proof)]:
        obs += verify(premise, feedback=feedback)
    return obs
