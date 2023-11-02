# The prover

Your task is to implement `prove` in `prover.py` to discharge each of the authorization goals described in the previous section.
As discussed in lecture, your prover will make use of a set of tactics that you design to construct authorization proofs. A tactic is simply a class with the following signature:
```
class Tactic(ABC):

    @abstractmethod
    def apply(self, seq: Sequent) -> set[Proof]:
        return set([seq])
```
The `apply` method accepts a sequent, and generates a set of proofs. 

## Getting started

Begin by familiarizing yourself with the provided example tactics listed below, and read the  [Chaining Tactics](#chaining-tactics) section below.
Then, we recommend that you proceed roughly with the following steps.

1. Implement the `CertTactic` whose behavior was described in the example from the previous section. Doing so should allow you to use `ThenTactic` to complete the first authorization proof goal of the lab.
2. Develop a tactic that allows you to take advantage of the first delegation policy, which contains a single universal quantifier. You may use `InstantiateForallTactic`, but it may help to first attempt the proof manually to see how to use this tactic effectively. This will allow you to develop a `ThenTactic` that handles the second authorization proof goal, possibly using tactics that you developed for step 1.
3. Start a manual proof of the third authorization goal. Closing it out will be tedious, but likely unnecessary in order to gain enough insight to plan a tactic for this goal. To minimize the amount of additional work required, look for ways to reuse the tactics that you developed for earlier goals.

As you proceed, there are several things that may be helpful to keep in mind.

* Do not implement a prover that can handle more general delegation policies, or anything beyond the three goals of this lab. Your prover only needs to produce proofs for the policies and formulas given in the previous section, so don't do more work than necessary!
* When considering how to handle transitive delegation (i.e., the third authorization goal), look for ways to do "work" outside of tactics. For example, it may be wise to scan the assumptions in the sequent given to `prover` to first figure out which agents are involved in a delegation chain leading from `#root` to `#andrewid`, and use that information to determine which tactics to include in a sequence given to `ThenTactic`. This will allow the tactics themselves to be simpler and more narrowly-focused on making definite progress towards closing out a proof.
* Part of your grade will be calculated by the number of unnecessary credentials and certificates that your authorization requests contain: your proof should not rely on credentials that are not actually needed to make a successful authorization. You should consider this when designing tactics that deal with `sign(...)` formulas: they could all be converted to `says` formulas eagerly before doing anything else, but this would mean that your proof would always rely on *every* certificate and credential provided in the context. It is better to consider tactics that only make use of `sign` formulas when they are needed to make progress handling the delegation policy.
* It's fine to start small: write tactics that emulate the steps that you would take to complete a proof by hand, and test them early. Use these tactics as building blocks to handle more complex formulas, until you are able to complete the authorization requests described in the previous section.


## Provided examples
Several tactics are provided for you in `prover.py`. 

* `InstantiateForallTactic`: use the left universal quantifier rule to instantiate a quantified assumption with a chosen term to substitute in for the quantified variable. For example, a tactic constructed as `InstantiateForallTactic([Agent('#mfredrik')])` and applied to `@x . open(x, <r>) |- open(#andrewid, <r>)`, would yield a proof that applies `@L` once, ending with the (unclosed) sequent `open(#mfredrik, <r>) |- open(#andrewid, <r>)`.
* `SignTactic`: apply the `Sign` rule to a specified `sign` formula in the assumptions, replacing it with the corresponding `says` formula. The docstring for this tactic provides an example of its use.
* `RuleTactic`: apply a given proof rule, which is passed to the constructor. We detailed this tactic in lecture, and show examples of its use below.
* `ThenTactic`: apply a given sequence of tactics to make progress towards closing a proof. This is the most important "meta" tactic that you will use, as it allows you to chain tactics together, mirroring the process that you would take to writing a proof manually.
* `OrElseTactic`: given a sequence of tactics, apply them (in order) until one makes progress. Once progress has been made, exit the tactic.

## Chaining Tactics

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

## Tip: don't forget to `Cut`

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