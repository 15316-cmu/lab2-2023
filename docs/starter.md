# Getting started

Clone this repository onto your local machine or your Andrew home directory.

You will need to use Python 3.10 to complete this lab. You can reuse the virtual environment that you created for Lab 1. The only new dependency that you will need to complete the lab is the `cryptography` modulo, which you can install either via `pip` or `conda` from within your environment.
```
> [pip|conda] install cryptography
```
You should then copy your private key, along with the credentials that you will need into the repository directory. Assuming `<id>` is your Andrew ID, run the following command:
```
scp -r <id>@linux.andrew.cmu.edu:/afs/andrew.cmu.edu/usr8/mfredrik/15316-f23/<id>/* .
```

## Credentials
You should now have a `credentials` directory with the following contents:
```
<id>_secret.cred
<id>_shared.cred
<id>_txt.cred
dsduena_secret.cred
justinyo_secret.cred
mdhamank_secret.cred
mfredrik_secret.cred
mfredrik_shared.cred
policy1.cred
policy2.cred
siruih_secret.cred
```
A *credential* is a formula expresses the policy intent of an agent, that is signed by their private key to provide authenticity. For example, `policy1.cred` contains the following:
```
{
  "p": "(@A . (((#mfredrik says open(A, <shared.txt>)) -> open(A, <shared.txt>))))",
  "signator": "#root",
  "signature": "c397b1d047279a4f544ae7eecafed3939b2780bc4f61b443849ec62069ce2b8353c5805cb102753f9b309d12541cc25349cced3cb830a137e30610f677068d02"
}
```
Here, `p` contains the policy formula, `signator` refers to the agent who signed the formula, and the bytes of the actual digital signature are given in `signature`.
We are more familiar working with credentials as `sign` formulas, and we can get such a formula from the credential, and pretty-print it using `util.stringify`:
```
> import crypto, util
> cred = crypto.Credential.load_credential('credentials/policy1.cred')
> print(stringify(cred.sign_formula()))
sign(((@A . (((#mfredrik says open(A, <shared.txt>)) -> open(A, <shared.txt>))))), [2b:8f:e8:9b])
```
The second argument appearing in square brackets is a digest of the signer's public key.

Each policy used in this lab has a corresponding credential; the details of those policies are described in the implementation section of this documentation.
You do not need to worry about manually loading credentials in most cases, as `auth.load_all_credentials` will do it for you.

## Certificates
You should now have a `certs` directory with the following files (assuming `<id>` is your Andrew ID).
```
<id>.cert
ca.cert
dsduena.cert
justinyo.cert
mdhamank.cert
mfredrik.cert
root.cert
siruih.cert
```
A *certificate* is a formula in which a certificate authority (identified by `#ca` in this lab) signs that a public key belongs to a given agent:
```
sign(iskey(#agent, [agent_key_fingerprint]), [ca_key_fingerprint])
```
A key fingerprint is a string that uniquely identifies a public key, for example `[68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40]`.

<details>
<summary>What's in a certificate?</summary>

Looking at `certs/root.cert`, the contents are as follows.
```
{
  "agent": "#root",
  "cred": {
    "p": "iskey(#root, [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])",
    "signator": "#ca",
    "signature": "4c120014db10eade1ab7a14f6745c94067f13bb38e4424c8084c24688a062268db37a08f480f571c90700afae07070c96428965cd19d20d3d2f105231ee60706"
  },
  "public_key": "2d2d2d2d2d424547494e205055424c4943204b45592d2d2d2d2d0a4d436f77425159444b32567741794541506844563357384a466d45547767366d69396b416262484e2b5742506c4e586f743372486f36466e5430303d0a2d2d2d2d2d454e44205055424c4943204b45592d2d2d2d2d0a"
}
```
Notice that the actual formula is given in `cert.cred.p`, in addition to easily-accessible metadata such as which party's public key is being certified (`cert.agent = #root`) and who the CA is (`cert.cred.signator = ca`).

<p>

Additionally, certificate files contain the base64-encoded digital signature (`cert.cred.signature`), signed using the public key of `cert.cred.signator`, as well as the public key of `cert.agent` (in this case, `#root`) in `cert.public_key`. If `#root` were to sign a credential, then it could be verified using this public key.
</details>

## Private keys
Finally, in the `private_keys` directory, you should see:
```
<id>.pem
```
You do not need to worry about the specific details of private keys, and you will not need to work directly with them: the code handed out with this lab takes care of creating signatures and certificates from private keys that you have access to.
The APIs for doing this are discussed in more detail in [exploiting a vulnerability](exploit.md).

## Authorization Logic

`logic.py` defines the authorization logic that we have discussed in class. 
There are three types of constants: agents, keys, and resources. 

* `Agent` constants are prefixed with `#`.
* `Key` constants appear between brackets `[]`.
* `Resource` constants appear between angle brackets `<>`.

In formulas, locations expecting a constant of a particular type can also recieve a variable, which is just an alphanumeric string that is not prefixed with any special characters. 
Both of the following are syntactically valid formulas, where the first has three variables that are replaced by corresponding constants in the second.
```
A says open(B, R)
#A says open(#B, <R>)
```
A parser is provided in `parser.py`, and we strongly recommend that you use the parser to construct formula objects, rather than building them manually from the constructors in `logic.py`.
```
> parse('A says P')
App(op=<Operator.SAYS: 7>, arity=2, args=[Variable(id='A'), Variable(id='P')])
```
The logic supports universal quantifiers, and uses the `@` symbol for them.
When parsing quantified formulas, note that you should surround the quantified formula with parentheses to avoid potential parser errors. 
So the following may result in a parser error. 
```
parse('@x . @y . open(x, y)')
```
It should be run as follows.
```
parse('@x . (@y . (open(x, y)))')
```

### Sequents and judgements

When building sequents, our authorization logic distinguishes between affirmation justdments and truth judgements.
Truth judgements are denoted by writing `true` after a formula, and are represented by the `Proposition` class in `logic.py`.
```
> parse('(P -> Q) true')
Proposition(p=App(op=<Operator.IMPLIES: 4>, arity=2, args=[Variable(id='P'), Variable(id='Q')]))
```
Affirmation judgements are denoted by juxtaposing a principal, `aff`, and a formula.
```
> parse('A aff P -> Q')
Affirmation(a=Variable(id='A'), p=App(op=<Operator.IMPLIES: 4>, arity=2, args=[Variable(id='P'), Variable(id='Q')]))
```
Sequents are expressed using `|-`, and accept either type of judgement on the right.
```
> parse('P |- A aff P')
Sequent(gamma=[Proposition(p=Variable(id='P'))], delta=Affirmation(a=Variable(id='A'), p=Variable(id='P')))
```
Note that if you do not write `true` to expressly denote a truth judgement, the parser will assume that this was what you intended to do.
```
> parse('P |- Q')
Sequent(gamma=[Proposition(p=Variable(id='P'))], delta=Proposition(p=Variable(id='Q')))
```

### Proof rules
The proof rules available in this logic are listed in `proofrules.py`.
```
@dataclass(eq=True, frozen=True)
class Rule:
    premises: list[Sequent]
    conclusion: Sequent
    name: str
```
As one might expect, a rule is comprised of a list of premises, each its own sequent, and a conclusion sequent. The convention that we use for specifying premises and the conclusion is illustrated by the left implication rule.
```
Rule(
    [
        parse('|- P true'),
        parse('Q true |- R true')
    ],
    parse('P -> Q true |- R true'),
    '->L'
)
```
Proof rules and sequents are composed to build `Proof` objects.
```
@dataclass(eq=True, frozen=True)
class Proof:
    premises: list[Proof | Sequent]
    conclusion: Sequent
    rule: Rule
```
Each step of a proof much refer to a `Rule` defined in `proofrules.py`; you should not invent your own rules to use in proofs. Proofs are generated by *tactics* in this lab (more on this later), but for the purposes of illustration, we can manually write the following proof to reflect and application of the left implication rule.
```
Proof(
    [
        parse('(c -> d) -> e |- a'),
        parse('b, (c -> d) -> e |- f')
    ],
    parse('a -> b, (c -> d) -> e |- f'),
    impLeftRule
)
```
The `stringify` helper from `util.py` will print this out nicely.
```
   ((c -> d) -> e) true |- a true  b true, ((c -> d) -> e) true |- f true
->L ------------------------------------------------------------------------
                (a -> b) true, ((c -> d) -> e) true |- f true
```
Note that your proofs may become wider than your screen.
You can specify the width that `stringify` should be limited to with the `pf_width` keyword argument, and it will split premises apart from the main proof and print them separately.
```
> print(stringify(pf, pf_width=50))
                          T.0  T.1
->L --------------------------------------------------
      (a -> b) true, ((c -> d) -> e) true |- f true

Proof T.1:
b true, ((c -> d) -> e) true |- f true

Proof T.0:
((c -> d) -> e) true |- a true
```

Looking at the rules available in `proofrules.py`, most should be familiar from lecture. The exceptions are `impLeftAffRule`, `forallLeftAffRule`, and `affCutRule`.
```
impLeftAffRule = Rule(
    [
        parse('|- P true'),
        parse('Q true |- A aff R')
    ],
    parse('P -> Q true |- A aff R'),
    '->L'
)

forallLeftAffRule = Rule(
    [parse('P(e) |- A aff Q')],
    parse('@x . P(x) |- A aff Q'),
    '@L'
)

affCutRule = Rule(
    [
        parse('|- P true'),
        parse('P true |- A aff Q')
    ],
    parse('|- A aff Q'),
    'affcut'
)
```
These rules are the same as their "normal" counterparts from lecture, but they match sequents with an affirmation judgement on the right. You are free to use these rules when constructing `Proof` objects, and doing so should make developing tactics less intricate, as you have more freedom to decide when to apply the right `says` rule.

<details>

<summary>Full grammar of the logic</summary>

```
<agent>   ::= x                            // variable
            | #a                           // constant
            
<key>     ::= x                            // variable
            | [k]                          // constant
            
<resource> ::= x                           // variable
            | <r>                          // constant

<formula> ::= x                            // variable
            | <formula> -> <formula>       // implication
            | <agent> says <formula>
            | iskey(<agent>, <key>)
            | sign(<formula>, <key>)
            | ca(<agent>)
            | open(<agent>, <resource>)
            | @x . <formula>               // universal quantifier
            
<judgement> ::= <formula> true             // proposition
              | <agent> aff <formula>      // affirmation
              
<sequent> ::= <judgement>* |- <judgement>
```
</details>

## Next steps

Now that you're familiar with the building blocks needed to write authorization proofs, check out the [authorization goals](implementation.md) for the lab.