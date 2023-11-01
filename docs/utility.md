# Utility code

Before developing your implementation, you should have a look in `util.py`. This file contains several utility functions that are likely to be helpful with the tasks described above.

* `allvars`, `allkeys`, `agents`, and `resources` return sets of variables, keys, agents, or resources contained in formulas, sequents, and proofs.
* `fresh_var` returns a fresh variable that is not named within a formula, sequent, or proof.
* `is_ca_key` scans a sequent to determine whether a specified key belongs to a certificate authority.
* `get_cas` scans a sequent to return the set of agents named as certificate authorities by the `ca(*)` predicate.
* `get_ca_key` scans a sequent to find the set of public key fingerprints that are associated with certificate authorities.
* `is_key` scans a sequent to determine whether a public key fingerprint is associated with a specified agent.
* `is_credential` scans a sequent to determine whether a given formula is a credential signed by a specified agent.
* `has_credential` scans a sequent to determine whether a credential for a given formula, signed by a specified agent, exists in the context.
* There are `*_stringify` functions for formulas, sequents, and proofs. The function `stringify` function can be called on any of these objects, and dispatches to the correct stringifier.
* When calling `stringify` on a proof, you can pass the optional argument `trunc_context=True` to print the proof without the context (i.e., `gamma`) portion of sequents. This can make it easier to follow and debug when attempting to prove sequents with many assumptions.