from logic import Rule
from parser import parse

identityRule = Rule([], parse('P true |- P true'), 'id')

falseLeftRule = Rule([], parse('false true |- P true'), 'botL')

impRightRule = Rule([parse('P true |- Q true')], parse('|- P -> Q true'),
                    '->R')

impLeftRule = Rule(
    [parse('|- P true'), parse('Q true |- R true')],
    parse('P -> Q true |- R true'), '->L')

impLeftAffRule = Rule(
    [parse('|- P true'), parse('Q true |- A aff R')],
    parse('P -> Q true |- A aff R'), '->Laff')

forallRightRule = Rule([parse('|- P(y)')], parse('|- @x . P(x)'), '@R')

forallLeftRule = Rule([parse('P(e) |- Q')], parse('@x . P(x) |- Q'), '@L')

forallLeftAffRule = Rule([parse('P(e) |- A aff Q')],
                         parse('@x . P(x) |- A aff Q'), '@Laff')

weakenRule = Rule([parse('Q true |- R true')],
                  parse('P true, Q true |- R true'), 'W')

cutRule = Rule(
    [parse('|- P true'), parse('P true |- Q true')], parse('|- Q true'), 'cut')

affCutRule = Rule(
    [parse('|- P true'), parse('P true |- A aff Q')], parse('|- A aff Q'),
    'affcut')

affRule = Rule([parse('|- P true')], parse('|- A aff P'), 'aff')

saysLeftRule = Rule([parse('P true |- A aff Q')],
                    parse('A says P true |- A aff Q'), 'saysL')

saysRightRule = Rule([parse('|- A aff P')], parse('|- A says P true'), 'saysR')

signRule = Rule([parse('|- iskey(A, pk) true'),
                 parse('|- sign(P, pk) true')], parse('|- A says P true'),
                'sign')

certRule = Rule(
    [parse('|- ca(A) true'),
     parse('|- (A says iskey(B, pk)) true')], parse('|- iskey(B, pk) true'),
    'cert')

_defs = vars()
calculus = {
    _defs[v].name: _defs[v]
    for v in vars() if isinstance(_defs[v], Rule)
}
