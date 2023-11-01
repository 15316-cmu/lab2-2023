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


In the `credentials` directory, you should have the following.
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
Finally, in the `private_keys` directory, you should see:
```
<id>.pem
```