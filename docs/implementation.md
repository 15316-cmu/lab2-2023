# Authorization goals

Your primary objective in the lab is to implement a prover that construct authorization proofs for three policies.

## Principals and high-level policies

The environment that these policies assume includes the following agents:

* `#ca`: the certificate authority
* `#root`: the agent who ultimately provisions authorization
* `#mfredrik`: authorized by `#root` to open `<shared.txt>` and `<secret.txt>`
* `#dsduenas`: authorized by `#mfredrik` to open `<secret.txt>`
* `#justinyo`: authorized by `#dsduenas` to open `<secret.txt>`
* `#mdhamank`: authorized by `#justinyo` to open `<secret.txt>`
* `#suruih`: authorized by `#mdhamank` to open `<secret.txt>`
* `#andrewid`: everyone in the class is authorized by `#root` to open `<andrewid.txt>`, by `#mfredrik` to open `#shared`, and by `#suruih` to open `<secret.txt>`.

## The details

You will first prove that you are able to open `<andrewid.txt>`, for your Andrew ID. For example, if your Andrew ID is `satoshi`, then your proof goal will be:
```
... |- #root says open(#satoshi, <satoshi.txt>)
```
The context, or assumptions left of the turnstile, that your prover will be given, is populated automatically from the certificates and credentials distributed with the lab (discussed later).
You should be able to use the credential in `andrewid_txt.cred` to discharge this goal. The credential consists of the following:
```
sign((open(#andrewid, <andrewid.txt>)), [2b:8f:e8:9b])
```
Your next objective will be the basic delegation policy, issued in `policy1.cred`:
```
sign(((@A . (((#mfredrik says open(A, <shared.txt>)) -> open(A, <shared.txt>))))), [2b:8f:e8:9b])
```
Your prover should use this policy to prove that you can open `<shared.txt>`:
```
... |- #root says open(#andrewid, <shared.txt>)
```
To complete this goal, you will also need to use the fact that `#mfredrik` is authorized by `#root` to open `<shared.txt>`, issued in `mfredrik_shared.cred`.

Finally, your prover will use the transitive delegation policy, also issued by `#root` in `policy2.cred`:
```
sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b])
```
To prove that you can access `<secret.txt>`:
```
... |- #root says open(#andrewid, <secret.txt>)
```
To complete this objective, you will need to also make use of the chain of credentials from `#root -> #mfredrik -> #dsduenas -> ... -> #andrewid`.

## Recommended: work it on paper first

Before moving on, we recommend that you work the following out on pencil and paper.

1. Identify which of the certificates and credentials above are necessary to prove the first (and most straightforward) goal.
2. Review using the `Cert` rule to prove `#ca says iskey(#root, [...])`.
3. Review using the `Sign` rule to prove `#root says open(#andrewid, <andrewid.txt>)`.
4. Put the pieces together to complete the proof of the first goal.

As you complete each proof goal, we suggest going back to this approach whenever you find yourself getting stuck. If you come to the course staff with questions, we will likely ask to see your work before providing assistance.

