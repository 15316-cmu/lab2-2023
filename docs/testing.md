# Testing your prover

The starter code in `prover.py` is configured to run your implementation of `prove` on a set of smaller tests in `prover_tests.txt` when invoked from the command line from the root of this repository.
```
> python src/prover.py
```
These tests are not graded, but they may be helpful when developing specific tactics as they have fewer assumptions, and require fewer proof steps to complete. The recommended way to use these tests is to start from the simpler formulas, develop tactics that can be sequenced together to complete them. Look to incrementally add functionality until you are able to complete the tests near the end of `prover_tests.txt`, which are qualitatively similar to the real proof goals of the lab. Note that when your `prove` function is able to complete the more realistic tests near the end, it may fail on earlier tests that look very different (e.g., cases that have `says` instead of `sign` formulas in their assumptions). This is expected, and you are not graded on these test cases.

Note that as you complete more of the lab, your prover may not be configured to solve each of the sequents in `prover_tests.txt` directly, as they look 

When you believe that your prover is able to handle the actual delegation policies, run `auth.py`, giving it an `agent` and a `resource` as arguments: 
```
> python src/auth.py agent resource
```
it gathers the assumptions discussed in the previous section into a context `Gamma`, constructs the sequent `Gamma |- #root says open(#agent, <resource>)`, and calls your prover. If your prover finds a proof, then `auth.py` scans the proof to determine which credentials and certificates it uses, and constructs an authorization request containing your proof along with all of the necessary credentials and certificates to verify it.

You may run `auth.py` with the `-s` flag, and a request will be sent to an authorization server. If your proof verifies, and all of the credentials check out, then you will recieve a credential back from the server letting you know that `#root` grants access.

For reference, the following three commands correspond to the proof goals for this lab:
```
> python src/auth.py -s andrewid andrewid.txt
> python src/auth.py -s andrewid shared.txt
> python src/auth.py -s andrewid secret.txt
```
If you see credentials like the following, then you have successfully completed this part of the lab.
```
************************ Credential ************************
statement: open(#andrewid, <secret.txt>)
signator: #root
signature: [63:7f:5f:b7:11:4e:b8:e7:55:dd:96:01:8d:13:88:75]
************************************************************
```