# Implementing your prover

## Authorization Logic

The logic is defined in `logic.py`. It is the same authorization logic that we have discussed in class. Note that there are three types of constants: agents, keys, and resources. 
* `Agent` constants are always prefixed with `#`.
* `Key` constants appear between brackets `[]`.
* `Resource` constants appear between angle brackets `<>`.
In formulas, locations expecting a constant of a particular type can also recieve a variable. So both of the following are syntactically valid formulas.
```
A says open(B, R)
#A says open(#B, <R>)
```
A parser is provided in `src/parser.py`, so you can construct, for example, a sequent object by calling:
```
parse('P true, Q true |- A aff Q')
```
Note that writing `true` after truth (`Proposition`) judgements is optional for the parser. When parsing quantified formulas, note that you should surround the quantified formula with parentheses to avoid potential parser errors. So running,
```
parse('@x . @y . open(x, y)')
```
may result in a parser error. It should be run as follows:
```
parse('@x . (@y . (open(x, y)))')
```

<details>
    <summary><b>Further details: grammar, rules, and proofs</b></summary>

The full grammar is given below. 
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

The proof rules available in this logic are listed in `proofrules.py`. The constructor for proof rules is given in `logic.py`.
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
Note that the indeterminate $\Gamma$ that is universally present in the typeset versions of rules in the lecture notes is missing. We assume that this is always present, and that rules can be matched against sequents that contain arbitrary sequences of judgements on the left of the turnstile. So the following sequents would all match this left implication rule:
```
a, b, c, d -> e |- f
a -> b |- f -> a
sign(iskey(#a, [k1]), [k2]), iskey(#a, [k1]) -> (#a says P), iskey(#b, [k2]) |- #a says Q
```
And the following would not, because there is no implication among the assumptions in the sequent:
```
sign(iskey(#a, [k1]) -> (#a says P), [k2]), iskey(#b, [k2]) |- #a says Q
```
Rules are matched to sequents as described in lecture, and illustrated in `RuleTactic` (`prover.py`). Essentially, a sequent is first matched to the conclusion of a rule, to obtain one or more substitutions (by `matchs_sequent` in `logic.py`). For the following sequent, the left implication rule would match in two ways:
```
a -> b, (c -> d) -> e |- f
```
The two distinct matchings yield the following substitutions from variables in the proof rule to formulas in the sequent:
```
Substitution 1: P => a, Q => b, R => f
Substitution 2: P => c -> d, Q => e, R => f
```
The substitutions obtained by matching the conclusion are applied to the premises of the proof rule, generating two new proof objectives for each substitution. For the first substitution,
```
(c -> d) -> e |- a          (from the first rule premise)
b, (c -> d) -> e |- f       (from the second rule prmise)
```
And for the second substitution:
```
a -> b |- c -> d
a -> b, e |- f
```
Note that `RuleTactic` does not work for the quantifier rules `@L`, `@R`, and you will need to implement tactics for these formulas as discussed later in this readme.

As illustrated in `RuleTactic`, proof rules are needed when constructing `Proof` objects (defined in `logic.py`).
```
@dataclass(eq=True, frozen=True)
class Proof:
    premises: list[Proof | Sequent]
    conclusion: Sequent
    rule: Rule
```
Each step of a proof much refer to a `Rule` defined in `proofrules.py`; you should not invent your own rules to use in proofs. Proofs are generated by `Tactic` objects (discussed in more detail below), but constructing them is straightforward. For example, we can manually write the following proof to reflect the first application of the left implication rule illustrated above.
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
The identifier `impLeftRule` comes from `proofrules.py`. This pretty-prints as follows, using the `stringify` function in `util.py`:
```
   ((c -> d) -> e) true |- a true  b true, ((c -> d) -> e) true |- f true
->L ------------------------------------------------------------------------
                (a -> b) true, ((c -> d) -> e) true |- f true
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
</details>

### Proof goals

For this lab, you will implement a prover that is able to construct authorization proofs for two delegation policies. The environment that these policies assume consists of the following agents:
* `#ca`: the certificate authority
* `#root`: the agent who ultimately provisions authorization
* `#mfredrik`: authorized by `#root` to open `<shared.txt>` and `<secret.txt>`
* `#aditi`: authorized by `#mfredrik` to open `<secret.txt>`
* `#jack`: authorized by `#aditi` to open `<secret.txt>`
* `#nuno`: authorized by `#jack` to open `<secret.txt>`
* `#andrewid`: everyone in the class is authorized by `#root` to open `<andrewid.txt>`, by `#mfredrik` to open `#shared`, and by `#nuno` to open `<secret.txt>`.

You will first want to prove that you are able to open `<andrewid.txt>`, for your Andrew ID.
```
... |- #root says open(#andrewid, <andrewid.txt>)
```
You will then use the basic delegation policy, issued as a credential by `#root`:
```
#root says (@A . ((#mfredrik says open(A, <shared.txt>)) 
                    -> open(A, <shared.txt>)))
```
Your prover should use this policy to prove that you can open `<shared.txt>`:
```
... |- #root says open(#andrewid, <shared.txt>)
```
Finally, your prover will use the transitive delegation policy, also issued by `#root`:
```
#root says (@A . (@R . (open(A, R) -> (@B . ((A says open(B, R)) 
                                        -> open(B, R))))))
```
To prove that you can access `<secret.txt>`:
```
... |- #root says open(#andrewid, <secret.txt>)
```
The context, or assumptions left of the turnstile, that your prover will be given, is populated automatically from the certificates and credentials (in the `certs` and `credentials` directories) distributed with the lab.

A *certificate* is a formula in which a certificate authority (identified by `#ca` in this lab) signs that a public key belongs to a given agent:
```
sign(iskey(#agent, [agent_key_fingerprint]), [ca_key_fingerprint])
```
A key fingerprint is a string that uniquely identifies a public key, for example `[68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40]`.

A *credential* is a formula that is signed by an agent to express authentic intent. For example, in `policy1.cred`, `#root` signs the first delegation policy above. This becomes an assumption in the prover's context:
```
sign(((@A . (((#mfredrik says open(A, <shared.txt>)) -> open(A, <shared.txt>))))), [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22])
```
Note that `#root` does not appear in this formula, but we can check that `[88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22]` is the public key belonging to `#root` by noting that there is a certificate loaded in to the context that associates this key with `#root`, signed by `#ca`:
```
sign((iskey(#root, [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22])), [68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40])
```
Recall that our logic allows converting `sign` formulas into `says`, so each credential and certificate can be used to derive a corresponding `says` formula.

When your prover is loaded, assuming that you have removed unnecessary certificates and credentials as [outlined earlier](#getting-started), the following context will be present as assumptions for your prover to use.
```
ca(#ca) true,
iskey(#ca, [68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40]) true,
sign((iskey(#nuno, [33:37:30:b5:9c:82:c6:0a:44:e9:06:8c:59:cd:f7:dc])), [68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40]) true,
sign((iskey(#mfredrik, [2c:e6:6b:45:6f:cc:d7:b9:e9:bf:2b:a1:ec:62:8e:cf])), [68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40]) true,
sign((iskey(#root, [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22])), [68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40]) true,
sign((iskey(#aditi, [38:24:c8:d0:bc:d5:e6:31:7b:91:97:0f:82:b0:4e:72])), [68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40]) true,
sign((iskey(#jack, [98:50:c6:80:ae:eb:1e:46:bf:a8:67:61:03:83:bc:56])), [68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40]) true,
sign((open(#andrewid, <secret.txt>)), [33:37:30:b5:9c:82:c6:0a:44:e9:06:8c:59:cd:f7:dc]) true,
sign((open(#andrewid, <shared.txt>)), [2c:e6:6b:45:6f:cc:d7:b9:e9:bf:2b:a1:ec:62:8e:cf]) true,
sign((open(#andrewid, <andrewid.txt>)), [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22]) true,
sign((open(#aditi, <secret.txt>)), [2c:e6:6b:45:6f:cc:d7:b9:e9:bf:2b:a1:ec:62:8e:cf]) true,
sign((open(#jack, <secret.txt>)), [38:24:c8:d0:bc:d5:e6:31:7b:91:97:0f:82:b0:4e:72]) true,
sign((open(#mfredrik, <secret.txt>)), [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22]) true,
sign((open(#mfredrik, <shared.txt>)), [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22]) true,
sign((open(#nuno, <secret.txt>)), [98:50:c6:80:ae:eb:1e:46:bf:a8:67:61:03:83:bc:56]) true,
sign(((@A . (((#mfredrik says open(A, <shared.txt>)) -> open(A, <shared.txt>))))), [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22]) true,
sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22]) true
```

#### Getting started

Before moving on, we recommend that you work the following out on pencil and paper.
1. Identify which of the certificates and credentials above are necessary to prove the first goal `#root says open(#andrewid, <andrewid.txt>)`.
2. Review using the `Cert` rule to prove `#ca says iskey(#root, [...])`.
3. Review using the `Sign` rule to prove `#root says open(#andrewid, <andrewid.txt>)`.
4. Put the pieces together to complete the proof of the first goal.

As you complete each proof goal, you may want to repeat parts of this pencil-and-paper exercise before implementing a prover for the next (more complex) goal.

<details>
    <summary><b>Optional reading: further details on credentials and certificates</b></summary>

In each of the sequents that you will prove above, the context (i.e., assumptions to the left of the sequent) is given by the set of credentials and certificates distributed with the lab in the `credentials` and `certs` directories, respectively. 

Each credential is a formula signed by another agent. For example, the following credential is signed by `#root`, and says that `#andrewid` is authorized to open `<andrewid.txt>`.
```
{
  "p": "open(#andrewid, <andrewid.txt>)",
  "signator": "#root",
  "signature": "5abc0a47a09d39e22f37f98791a108add35ca0bf85f84ab0a13462dc9206dddab6fbc4e7a5daf59c425622aa9a6009806983ba5c16d69c40ad5976e95edf230e"
}
```
Each policy in the bulleted list above, as well as the two delegation policies just discussed, has a corresponding credential in this directory. 

Each certificate is a public key, associated with an agent, and signed by the `#ca` agent. The certificate for `#root` is shown below.
```
{
  "agent": "#root",
  "cred": {
    "p": "iskey(#root, [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22])",
    "signator": "#ca",
    "signature": "91aa08822ebc913109d4cac15ddfa0165d8a1166cacf303c560d888a245c36fe4873519f3e45e065b551c1de44fc708b5add3713f5188af19720920f9dddca02"
  },
  "public_key": "2d2d2d2d2d424547494e205055424c4943204b45592d2d2d2d2d0a4d436f77425159444b32567741794541644c6c416a767751693954302b543765544f726d524c506f67426f346d34327056483246597877355858773d0a2d2d2d2d2d454e44205055424c4943204b45592d2d2d2d2d0a"
}

```

When you run `auth.py`, your prover will be called after populating the context with all of the credentials in this directory.

Each credential is added as a `sign` formula. For the example credential shown above, if is the public key fingerprint of `#andrewid`, then the following formula is added as an assumption). Note that the key matches the public key fingerprint listed in the certificate for `#root`.
```
sign(open(#andrewid, <andrewid.txt>), [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22])
```

Each certificate is added as a `sign(iskey(...))` formula, signed with the key of `#ca`. So the example certificate for `#root` shown above would become the following assumption.
```
sign(
    iskey(#root, [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22]),
    [68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40]
)
```
Finally, the following assumptions are always added, to establish that `#ca` is the trusted certificate authority, and that their key is already known.
```
ca(#ca)
iskey(#ca, [68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40])
```
</details>

### Tactics

Your task is to implement `prove` in `prover.py` to discharge each of the authorization goals described in the previous section.
As discussed in lecture, your prover will make use of a set of tactics that you design to construct authorization proofs. A tactic is simply a class with the following signature:
```
class Tactic(ABC):

    @abstractmethod
    def apply(self, seq: Sequent) -> set[Proof]:
        return set([seq])
```
The `apply` method accepts a sequent, and generates a set of proofs. 
Several tactics are provided for you in `prover.py`. 
* `InstantiateForallTactic`: use the left universal quantifier rule to instantiate a quantified assumption with a chosen term to substitute in for the quantified variable. For example, a tactic constructed as `InstantiateForallTactic([Agent('#mfredrik')])` and applied to `@x . open(x, <r>) |- open(#andrewid, <r>)`, would yield a proof that applies `@L` once, ending with the (unclosed) sequent `open(#mfredrik, <r>) |- open(#andrewid, <r>)`.
* `SignTactic`: apply the `Sign` rule to a specified `sign` formula in the assumptions, replacing it with the corresponding `says` formula. The docstring for this tactic provides an example of its use.
* `RuleTactic`: apply a given proof rule, which is passed to the constructor. We detailed this tactic in lecture, and show examples of its use below.
* `ThenTactic`: apply a given sequence of tactics to make progress towards closing a proof. This is the most important "meta" tactic that you will use, as it allows you to chain tactics together, mirroring the process that you would take to writing a proof manually.
* `RepeatTactic`: apply a given tactic repeatedly until no further progress can be made. You are welcome to use this tactic, but it is not necessary to complete this lab, and we warn that **this tactic can make it more difficult to debug your solution**. Do not use this tactic unless you are confident that it will behave as you expect.
* `OrElseTactic`: given a sequence of tactics, apply them (in order) until one makes progress. Once progress has been made, exit the tactic.

<details>
<summary><b>Chaining Tactics</b></summary>

Although we did not describe it as such, we have been using tactics throughout the semester when we demonstrate reasoning using formal inference rules and sequent proofs.
For example, to write a proof for the sequent:
```
R |- P -> Q -> R
```
You may immediately think, "apply the right implication rule twice, and then apply the identity rule to close the proof".
This approach is formalized by composing `ThenTactic` with several instances of `RuleTactic`.
```
t = ThenTactic([
    RuleTactic(impRightRule),
    RuleTactic(impRightRule),
    RuleTactic(identityRule)
])
```
Applying the above tactic to the sequent in question yields a losed proof.
```
                          *
      id ------------------------------------
           Q true, P true, R true |- R true
   ->R ------------------------------------------
           R true, P true |- (Q -> R) true
->R -------------------------------------------------
            R true |- (P -> (Q -> R)) true
```
Under the hood, `ThenTactic` accomplishes this by chaining incomplete proofs together.
After applying the first `RuleTactic(impRightRule)`, the (single) resulting proof is:
```
   P true, R true |- (Q -> R) true
->R ---------------------------------
    R true |- (P -> (Q -> R)) true
```
`ThenTactic` checks to see if this proof has any unclosed branches, and finds that there is one branch that progress can be made on by applying the next rule.
```
P true, R true |- (Q -> R) true
```
Applying the next tactic passed to `ThenTactic`, to attempt a proof of the sequent directly above, yields another unfinished proof.
```
   P true, R true, Q true |- R true
->R ----------------------------------
    P true, R true |- (Q -> R) true
```
`ThenTactic` finds the unfinished premise, and applies the final `RuleTactic(identityRule)`, to close it out.
```
                    *
id ------------------------------------
     P true, R true, Q true |- R true
```
Each time that `ThenTactic` applies the next tactic to derive a proof for an open branch, it substitutes the unfinished branch with that proof. For example, `P true, R true, Q true |- R true` from the penultimate proof is substituted with the proof directly above to work, in a backwards fashion, towards the original goal.
```
                       *
   id ------------------------------------
        Q true, P true, R true |- R true
->R ------------------------------------------
        P true, R true |- (Q -> R) true
```
Chaining this proof with the original unfinished branch, `P true, R true |- (Q -> R) true`, completes the proof.

This approach can also be used to transform assumptions to the left of the sequent.
Suppose that we have in our assumptions `iskey(#ca, [kca])`, `sign((iskey(#root, [kr])), [kca])`, and `sign((open(#a, <a.txt>)), [kr])`.
We want to prove that `#root says open(#a, <a.txt>)`.
If we were to implement a `CertTactic`, which takes an agent named in a certificate, their public key fingerprint, an agent who is a certificate authority, and the authority's public key certificate, then we might attempt to prove this goal with the following tactic.
```
t = ThenTactic([
    SignTactic(parse('sign(iskey(#root, [kr]), [kca])'), Agent('#ca')),
    CertTactic(Agent('#root'), Key('[kr]'), Agent('#ca'), Key('[ca]')),
    SignTactic(parse('sign((open(#a, <a.txt>)), [kr])'), Agent('#root')),
    RuleTactic(identityRule)
])
```
Now we can think through the steps that `ThenTactic` will take.
First applying `SignTactic` will yield a proof with two branches, `T.0` and `T.1`.
```
                                                           T.0  T.1
cut --------------------------------------------------------------------------------------------------------------------------
      iskey(#ca, [kca]), sign((iskey(#root, [kr])), [kca]), sign((open(#a, <a.txt>)), [kr]) |- #root says open(#a, <a.txt>)
```
The left branch `T.0` is a short proof that uses the `Sign` rule to prove `(#ca says iskey(#root, [kr]))` from the assumptions listed above.
This branch is already closed, because `iskey(#ca, [kca])` and `sign((iskey(#root, [kr]), [kca])` are already in the assumptions.
The right branch `T.1`, on the other hand, is just the following sequent:
```
iskey(#ca, [kca]), sign((open(#a, <a.txt>)), [kr]), (#ca says iskey(#root, [kr])) |- (#root says open(#a, <a.txt>))
```
`ThenTactic` will apply the next tactic to continue making progress on it, but observe that the formula `sign((iskey(#root, [kr]), [kca])` has been replaced with `#ca says iskey(#root, [kr])`.
This is useful, because the `Cert` rule has as a premise that if we want to derive `iskey(#root, [kr])`, then we need to prove `ca(#ca)` and `#ca says iskey(#root, [kr])`.
Thus, to implement `CertTactic`, we want its `apply` method to take a sequent like the one above, and produce a proof like the following:
```
                                                        T.0  T.1
cut -------------------------------------------------------------------------------------------------------------------
      iskey(#ca, [kca]), sign((open(#a, <a.txt>)), [kr]), #ca says iskey(#root, [kr]) |- #root says open(#a, <a.txt>)
```
Where `T.0` is a short, closed proof that applies the `Cert` rule to prove `iskey(#root, [kr])`, and `T.1` is the following sequent which incorporates that result as an assumption:
```
iskey(#ca, [kca]), sign((open(#a, <a.txt>)), [kr]), iskey(#root, [kr]) |- #root says open(#a, <a.txt>)
```
This allows `ThenTactic` to apply the next tactic, `SignTactic(parse('sign((open(#a, <a.txt>)), [kr])'), Agent('#root'))`, to this sequent, yielding a new branch:
```
iskey(#ca, [kca]), #root says open(#a, <a.txt>), iskey(#root, [kr]) |- #root says open(#a, <a.txt>)
```
Finally, `ThenTactic` can close this one remaining branch with `RuleTactic(identityRule)`, and chain the intermediate proofs together to finish up.

This is the approach that you should aim to take when developing your solution: write short, narrowly-focused tactics that can be combined with others using `ThenTactic` to complete proofs for each of the three goals.
Develop insights for which tactics you need to write from your experience working through proofs manually, so that the sequence of tactics that you give to `ThenTactic` mirror your knowledge of how to complete sequent proofs of authorization logic formulas.
</details>

#### Getting started

If you have not read the previous section, **Chaining Tactics** do so first.
1. Implement the `CertTactic` whose behavior was described in the example from the previous section. Doing so should allow you to use `ThenTactic` to complete the first authorization proof goal of the lab.
2. Develop a tactic that allows you to take advantage of the first delegation policy, which contains a single universal quantifier. You may use `InstantiateForallTactic`, but it may help to first attempt the proof manually to see how to use this tactic effectively. This will allow you to develop a `ThenTactic` that handles the second authorization proof goal, possibly using tactics that you developed for step 1.
3. Start a manual proof of the third authorization goal. Closing it out will be tedious, but likely unnecessary in order to gain enough insight to plan a tactic for this goal. To minimize the amount of additional work required, look for ways to reuse the tactics that you developed for earlier goals.

As you proceed, there are several things that may be helpful to keep in mind.
* Do not implement a prover that can handle more general delegation policies, or anything beyond the three goals of this lab. Your prover only needs to produce proofs for the policies and formulas given in the previous section, so don't do more work than necessary!
* When considering how to handle transitive delegation (i.e., the third authorization goal), look for ways to do "work" outside of tactics. For example, it may be wise to scan the assumptions in the sequent given to `prover` to first figure out which agents are involved in a delegation chain leading from `#root` to `#andrewid`, and use that information to determine which tactics to include in a sequence given to `ThenTactic`. This will allow the tactics themselves to be simpler and more narrowly-focused on making definite progress towards closing out a proof.
* Part of your grade will be calculated by the number of unnecessary credentials and certificates that your authorization requests contain: your proof should not rely on credentials that are not actually needed to make a successful authorization. You should consider this when designing tactics that deal with `sign(...)` formulas: they could all be converted to `says` formulas eagerly before doing anything else, but this would mean that your proof would always rely on *every* certificate and credential provided in the context. It is better to consider tactics that only make use of `sign` formulas when they are needed to make progress handling the delegation policy.
* It's fine to start small: write tactics that emulate the steps that you would take to complete a proof by hand, and test them early. Use these tactics as building blocks to handle more complex formulas, until you are able to complete the authorization requests described in the previous section.

<details>
    <summary><b>Tip: don't forget to `Cut`</b></summary>

In lecture we mentioned that the authorization logic does not need the `Cut` rule: any proof that uses `Cut` can be rewritten without it. However, your tactics are free to produce proofs that use `Cut`, and you may find that it is more straightforward to use `Cut` when the `Sign` and `Cert` rules are needed than otherwise. Consider the following sequent, which we will refer to as `seq1`.
```
ca(#ca),
iskey(#ca, [k1]),
sign(iskey(#a, [k2]), [k1]),
sign(iskey(#b, [k3]), [k1]),
sign((#a says open(#c, <r>)) -> open(#c, <r>), [k3])
sign(open(#c, <r>), [k2])
    |- #b says open(#c, <r>)
```
A proof for this needs to accomplish the following.

1. "Unwrap" the certificates `sign(iskey(#a, [k2]), [k1])` and `sign(iskey(#b, [k3]), [k1])` to establish that `[k2]` belongs to `#a` and `[k3]` belongs to `#b`. Doing so entails obtaining `#ca says iskey(#a, [k2])` and `#ca says iskey(#b, [k3])` using the `Sign` rule.
2. Obtain `#b says ((#a says open(#c, <r>)) -> open(#c, <r>))` and `#a says open(#c, r)`.
3. Make use of the previous two formulas to get `#b says open(#c, <r>)`.

The rules that are needed for (1) are `Cert` and `Sign`. The `Cert` rule applies when we have an `iskey(A, [k])` judgement on the right of the sequent. Likewise, `Sign` applies when we have `A says P` judgements on the right. This is true in our case, as we are trying to prove `#b says open(#c, <r>)`, but we also want to obtain `#a says open(#c, <r>)` from the formula signed by `[k2]`, and in any event, we can't use `Sign` directly to obtain `#b says open(#c, <r>)` because `#b` did not directly sign `open(#c, <r>)`.

The way to deal with this is to use `Cut` to formulate each goal that we need (and are able to prove from the existing assumptions), so that they become available in our assumptions for the rest of the proof. We could start by proving `#ca says iskey(#a, [k2])`.
```
p1 = Proof([p2, p3], parse('iskey(#ca, [k1]), sign(iskey(#a, [k2]), [k1]) |- #ca says iskey(#a, [k2])'), signRule)
```
The two premises of this proof themselves are proofs, which just apply the identity rule to show `iskey(#ca, [k1])` and `sign(iskey(#a, [k2]), [k1])`, respectively.
```
p2 = Proof([], parse('iskey(#ca, [k1]) |- iskey(#ca, [k1])'), identityRule)
p3 = Proof([], parse('sign(iskey(#a, [k2]), [k1]) |- sign(iskey(#a, [k2]), [k1])'), identityRule)
```
This gives us a proof that `#ca says iskey(#a, [k2])`, which we will need when applying the `Cert` rule to ultimately prove `iskey(#a, [k2])`. Let `seq2` be the following sequent, from which we can continue with the proof after using `Cut` to establish `#ca says iskey(#a, [k2])`.
```
ca(#ca),
iskey(#ca, [k1]),
#ca says iskey(#a, [k2])
sign(iskey(#b, [k3]), [k1]),
sign((#a says open(#c, <r>)) -> open(#c, <r>), [k3])
sign(open(#c, <r>), [k2])
    |- #b says open(#c, <r>)
```
The application of `Cut` is as follows.
```
Proof([p1, seq2], seq1, cutRule)
```
We can now continue the proof by working on `seq2`. The next step may be to apply `Cut` again, using the new assumption in `seq2` to prove `iskey(#a, [k2])` using `Cert`, so that it is available in the assumptions in the next sequent, in the right premise of that application of `Cut`.

Before moving on, careful readers may have noticed that the assumptions in the sequent proved in `p1` are a subset of those in our original goal, `seq1`. Technically, we would need to apply a rule (weakening) several times to remove certain assumptions before this would be allowed. In this lab, tactics may produce proofs that apply weakening (i.e., remove assumptions) without a corresponding step in the proof; the verifier will not reject this. This makes proofs shorter and easier to read when printed to standard output, and thus hopefully easier to debug.

</details>