# Authorization mechanics

An authorization server is running on port `15316` at `authproof.net`.
Its job is to accept credentials and authorization proofs, verify them, and provide new credentials that allow clients to access resources that the server controls.
It functions in the following way.

1. When a client connects on port `15316`, it expects to recieve an `AccessRequest` object (defined in `crypto.py`) containing a signed request for a named resource on behalf of a user, a proof that the user is allowed to access that resource, and any credentials and certificates needed to verify that the proof is correct.
2. The server calls `verify_request` (in `crypto.py`) on this access request.
3. If the request can be verified, then the server returns a new credential signed by `#root` granting access to the requested resource.
4. Otherwise, the server returns an error message.

The client is implemented in `auth.py`.
```
usage: auth.py [-h] [-s] requester resource

Constructs an authorization request, with proof. Optionally sends the request to the authorization server.

positional arguments:
  requester           agent making the request (use your andrew id)
  resource            resource under request (either shared.txt or andrewid.txt)

options:
  -h, --help          show this help message and exit
  -s, --send_request  send the request to the authorization server
```
Running the command `python src/auth.py andrewid andrewid.txt` will cause the following to happen.

## Step 1: Gather credentials

The client will first populate a sequent with a proof goal, filling the context with all of the certificates in `certs` and credentials in `cred`.
```
ca(#ca) true,
iskey(#ca, [43:c9:43:e6]) true,
sign((iskey(#mdhamank, [71:14:55:85])), [43:c9:43:e6]) true,
sign((iskey(#mfredrik, [d3:c6:2a:1b])), [43:c9:43:e6]) true,
sign((iskey(#root, [2b:8f:e8:9b])), [43:c9:43:e6]) true,
sign((iskey(#dsduena, [db:b2:b9:b7])), [43:c9:43:e6]) true,
sign((iskey(#justinyo, [d2:15:e7:01])), [43:c9:43:e6]) true,
sign((open(#andrewid, <andrewid.txt>)), [71:14:55:85]) true,
sign((open(#andrewid, <shared.txt>)), [d3:c6:2a:1b]) true,
sign((open(#andrewid, <andrewid.txt>)), [2b:8f:e8:9b]) true,
sign((open(#dsduena, <andrewid.txt>)), [d3:c6:2a:1b]) true,
sign((open(#justinyo, <andrewid.txt>)), [db:b2:b9:b7]) true,
sign((open(#mdhamank, <andrewid.txt>)), [d2:15:e7:01]) true,
sign((open(#mfredrik, <andrewid.txt>)), [2b:8f:e8:9b]) true,
sign((open(#mfredrik, <shared.txt>)), [2b:8f:e8:9b]) true,
sign(((@A . (((#mfredrik says open(A, <shared.txt>)) -> open(A, <shared.txt>))))), [2b:8f:e8:9b]) true,
sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b]) true,
sign((open(#siruih, <andrewid.txt>)), [71:14:55:85]) true
    |-  (#root says open(#andrewid, <andrewid.txt>)) true
```
Each credential is added as a `sign(open(...), [...])` formula. The credentials in this example are shown below.
```
sign((open(#andrewid, <andrewid.txt>)), [71:14:55:85]) true,
sign((open(#andrewid, <shared.txt>)), [d3:c6:2a:1b]) true,
sign((open(#andrewid, <andrewid.txt>)), [2b:8f:e8:9b]) true,
sign((open(#dsduena, <andrewid.txt>)), [d3:c6:2a:1b]) true,
sign((open(#justinyo, <andrewid.txt>)), [db:b2:b9:b7]) true,
sign((open(#mdhamank, <andrewid.txt>)), [d2:15:e7:01]) true,
sign((open(#mfredrik, <andrewid.txt>)), [2b:8f:e8:9b]) true,
sign((open(#mfredrik, <shared.txt>)), [2b:8f:e8:9b]) true,
sign(((@A . (((#mfredrik says open(A, <shared.txt>)) -> open(A, <shared.txt>))))), [2b:8f:e8:9b]) true,
sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b]) true,
sign((open(#siruih, <andrewid.txt>)), [71:14:55:85]) true
```
Each certificate is added as a `sign(iskey(...), [...])` formula, shown below.
```
sign((iskey(#mdhamank, [71:14:55:85])), [43:c9:43:e6]) true,
sign((iskey(#mfredrik, [d3:c6:2a:1b])), [43:c9:43:e6]) true,
sign((iskey(#root, [2b:8f:e8:9b])), [43:c9:43:e6]) true,
sign((iskey(#dsduena, [db:b2:b9:b7])), [43:c9:43:e6]) true,
sign((iskey(#justinyo, [d2:15:e7:01])), [43:c9:43:e6]) true
```
The certificate authority and their key are added to the assumptions.
```
ca(#ca) true,
iskey(#ca, [43:c9:43:e6]) true,
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
Finally, the request is reflected in the goal of the sequent. Namely, the user `#andrewid` requests access to `<andrewid.txt>`, and aims to show that this is authorized under `#root`'s policy.
```
(#root says open(#andrewid, <andrewid.txt>)) true
```

## Step 2: Call the prover

The `prove` function in `prover.py` is called on this sequent. It either returns a proof or `None`.

If the prover returns `None`, then the client prints a message and exits. Otherwise, the client begins generating a request to send to `authproof.net`.

## Step 3: Send the request

With a proof in hand, the client calls `generate_request` (in `auth.py`).
`generate_request` inspects the proof, and determins which credentials and certificates are needed to verify the proof.
In this example, only the credential in `andrewid_txt.cred`, which is signed by `#root` to state that `#andrewid` can open `<andrewid.txt>`, is needed.
Likewise, the only certificates that are needed are those of `#andrewid`, `#root`, and `#ca`.
It gathers these resources to attach to the request, signs the request with `#andrewid`'s secret key, and sends the request to the server.

The full request for this example is shown below.
```
signature:
*********************************** Credential ***********************************
statement: (#root says open(#andrewid, <andrewid.txt>))
signator: #andrewid
signature: [ef:63:cb:70:64:52:38:33:16:e6:88:e5:41:11:de:f7]
**********************************************************************************

credentials:
*********************************** Credential ***********************************
statement: open(#andrewid, <andrewid.txt>)
signator: #root
signature: [50:f0:40:3d:91:31:f3:ec:d2:99:bd:e6:b5:6c:8b:02]
**********************************************************************************

certificates:
============================= Public Key Certificate =============================
key: [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]
agent: #ca
*********************************** Credential ***********************************
statement: iskey(#ca, [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])
signator: #ca
signature: [4a:89:91:6e:c8:18:f2:d1:4c:c6:a0:b6:e8:cb:bf:44]
**********************************************************************************
==================================================================================
============================= Public Key Certificate =============================
key: [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]
agent: #root
*********************************** Credential ***********************************
statement: iskey(#root, [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])
signator: #ca
signature: [ac:84:67:26:09:c2:c0:39:0e:0a:13:70:f4:d7:3e:d2]
**********************************************************************************
==================================================================================
============================= Public Key Certificate =============================
key: [a2:56:e9:a5:c0:56:d9:32:7a:f1:5b:cb:ce:7a:13:47]
agent: #andrewid
*********************************** Credential ***********************************
statement: iskey(#andrewid, [a2:56:e9:a5:c0:56:d9:32:7a:f1:5b:cb:ce:7a:13:47])
signator: #ca
signature: [79:56:b9:1e:0d:a3:fd:4c:2e:72:f2:04:c3:38:fc:cb]
**********************************************************************************
==================================================================================
```

## Step 4: The response

If the server is able to verify that each certificate and credential was properly signed, and that the proof is correct, then it sends a fresh new credential signed by `#root` authorizing `#andrewid` to open `<andrewid.txt>`.

```
*********************************** Credential ***********************************
statement: open(#andrewid, <andrewid.txt>)
signator: #root
signature: [50:f0:40:3d:91:31:f3:ec:d2:99:bd:e6:b5:6c:8b:02]
**********************************************************************************
```

## Next steps

In the starter code, `prover.prove` always returns `None`. Your main job is to implement [the prover](tactics.md).

You do not need to change anything in `auth.py`, but it is good to understand how requests are generated and sent, and the role that your prover plays in this process.