from functools import lru_cache
from pyparsing import (
    AtStringStart,
    Regex,
    Word,
    Forward,
    Suppress,
    ParseResults,
    Opt,
    alphas,
    alphanums,
    delimited_list
)

from logic import (
    Operator,
    Variable,
    Agent,
    Resource,
    Key,
    App,
    Forall,
    Formula,
    Substitution,
    Proposition,
    Affirmation,
    Judgement,
    Sequent,
    Rule,
    Proof
)

def IdentParser():
    return Word(alphas, alphanums+'_'+'.')

def KeyParser():
    return Word(alphanums+':'+'_')

@lru_cache
def FormulaParser():
    fmla = Forward()

    true_const = Suppress("true").set_parse_action(lambda _: App(Operator.TRUE, 0, []))
    false_const = Suppress("false").set_parse_action(lambda _: App(Operator.FALSE, 0, []))
    vx = IdentParser().set_parse_action(lambda toks: Variable(toks[0]))
    ag = ('#' + IdentParser()).set_parse_action(lambda toks: Agent(toks[0] + toks[1]))
    key = ('[' + KeyParser() + ']').set_parse_action(lambda toks: Key(toks[0] + toks[1] + toks[2]))
    res = ('<' + IdentParser() + '>').set_parse_action(lambda toks: Resource(toks[0] + toks[1] + toks[2]))
    lpar, rpar = map(Suppress, "()")
    paren = lpar + fmla + rpar
    comma = Suppress(",")
    
    key_or_var = vx ^ key
    ag_or_var = vx ^ ag
    res_or_var = vx ^ res

    op_dict = {
        '->': Operator.IMPLIES,
        'says': Operator.SAYS,
        'sign': Operator.SIGN,
    }    
    implies_tok, says_tok, sign_tok = \
        map(lambda tok: Suppress(tok).set_parse_action(lambda _: op_dict[tok]), 
            ["->", "says", "sign"])
    ca = ('ca' + lpar + ag_or_var + rpar).set_parse_action(
        lambda toks: App(Operator.ISCA, 1, [toks[1]])
    )
    iskey = ('iskey' + lpar + ag_or_var + comma + key_or_var + rpar).set_parse_action(
        lambda toks: App(Operator.ISKEY, 2, toks[1:])
    )
    opens = ('open' + lpar + ag_or_var + comma + res_or_var + rpar).set_parse_action(
        lambda toks: App(Operator.OPEN, 2, toks[1:])
    )
    with_named_var = (vx + lpar + vx + rpar).set_parse_action(
        lambda toks: App(Operator.OTHER, 2, toks)
    )
    
    def parse_connective(toks: list) -> App:
        if len(toks) == 2:
            return App(toks[0], 1, [toks[1]])
        elif len(toks) == 3:
            if toks[0] == Operator.SIGN:
                return App(toks[0], len(toks)-1, toks[1:])
            else:
                return App(toks[1], len(toks)-1, [toks[0]] + toks[2:])
        else:
            raise ValueError('Parse error')
    
    atom = true_const | false_const | ca | iskey | opens | paren | with_named_var | vx
    sign_fmla = Forward()
    sign_fmla <<= atom \
        ^ (sign_tok + lpar + fmla + comma + key_or_var + rpar).set_parse_action(parse_connective)
    implies_fmla = Forward()
    implies_fmla <<= sign_fmla \
        ^ (implies_fmla + implies_tok + sign_fmla).set_parse_action(parse_connective)
    says_fmla = Forward()
    says_fmla <<= implies_fmla \
        ^ (ag_or_var + says_tok + implies_fmla).set_parse_action(parse_connective)
    fmla <<= says_fmla \
        ^ (Suppress("@") + vx + Suppress(".") + says_fmla).set_parse_action(
            lambda toks: Forall(toks[0], toks[1]))

    fmla.enable_left_recursion()
    return fmla

@lru_cache
def JudgementParser():
    fmla = FormulaParser()
    vx = IdentParser().set_parse_action(lambda toks: Variable(toks[0]))
    ag = ('#' + IdentParser()).set_parse_action(lambda toks: Agent(toks[0] + toks[1]))
    
    aff = (vx | ag) + Suppress('aff') + fmla
    aff.set_parse_action(lambda toks: Affirmation(toks[0], toks[1]))

    prop = fmla + Opt(Suppress('true'))
    prop.set_parse_action(lambda toks: Proposition(toks[0]))

    return aff ^ prop

@lru_cache
def SequentParser():
    judgement = JudgementParser()
    seq = Forward()
    
    def parse_sequent(toks: list) -> Sequent:
        return Sequent(toks[0], toks[1])
    
    j_list = delimited_list(judgement).add_parse_action(lambda toks: ParseResults.List(toks.as_list()))
    ts = Suppress("|-")
    
    no_gamma = ts + judgement
    no_gamma.set_parse_action(lambda toks: Sequent([], toks[0]))
    no_delta = j_list + ts
    no_delta.set_parse_action(lambda toks: Sequent(toks[0], App(Operator.FALSE, 0, [])))
    both_gd = j_list + ts + judgement
    both_gd.set_parse_action(lambda toks: Sequent(toks[0], toks[1]))
    
    seq <<= no_gamma ^ no_delta ^ both_gd
    
    return seq

def fmla_parse(s: str) -> Formula:
    return FormulaParser().parse_string(s, parse_all=True)[0]

def judgement_parse(s: str) -> Judgement:
    return JudgementParser().parse_string(s, parse_all=True)[0]

def sequent_parse(s: str) -> Sequent:
    return SequentParser().parse_string(s, parse_all=True)[0]

def parse(s: str):
    try:
        return fmla_parse(s)
    except:
        try:
            return judgement_parse(s)
        except:
            try:
                return sequent_parse(s)
            except BaseException as e:
                raise e