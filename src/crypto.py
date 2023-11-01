from __future__ import annotations
from dataclasses import dataclass, is_dataclass, asdict

from glob import glob
import hashlib
import json
import os

from cryptography.hazmat.primitives.asymmetric.ed25519 import (
	Ed25519PrivateKey,
	Ed25519PublicKey
)
from cryptography.hazmat.primitives.serialization import (
	Encoding, 
	PrivateFormat,
	PublicFormat,
	NoEncryption,
	load_pem_private_key,
	load_pem_public_key
)
from cryptography.hazmat.primitives.hashes import SHA256
from cryptography.hazmat.primitives.asymmetric.padding import MGF1, PSS
from cryptography.exceptions import InvalidSignature

from logic import *
from verifier import verify
from proofrules import calculus
from parser import parse, sequent_parse
from util import stringify

@dataclass(eq=True, frozen=True)
class Credential():

	"""
	Constructor for credential objects. Credentials are
	formulas signed by an agent, typically expressing authorization
	rights (e.g., `open` formulas) or private key vouchers 
	(e.g., `iskey` formulas).

	Args:
	    p (Formula): The signed statement
	    signator (Agent): The agent who issued (signed) the credential.
	    signature (str): A hexadecimal string representation of the
	    	signature created with `signator`'s private key on the
	    	message `stringify(p)`.
	"""
	
	p: Formula
	signator: Agent
	signature: str

	def serialize(self) -> str:
		return json.dumps(
			{
				'p': stringify(self.p),
				'signator': self.signator.id,
				'signature': self.signature
			},
			sort_keys=True,
			indent=2
		)

	@classmethod
	def from_json(cls, ser: str):
		ob = json.loads(ser)
		return cls(parse(ob['p']), Agent(ob['signator']), ob['signature'])

	@classmethod
	def from_formula(cls, p: Formula, agent: Optional[Agent]=None):
		"""
		Construct a credential from a formula. If `agent` is given,
		then the credential is signed with `agent`'s private key.
		Otherwise, `p` must be a `sign(P, [pk])` formula, and the
		private key corresponding to `[pk]` is retrieved from
		the `private_keys` directory and used to sign the
		credential.
		
		Args:
		    p (Formula): The formula to sign.
		    agent (Agent, optional): See the summary for a
		    	description of how this argument is used.
		
		Returns:
		    Credential: The credential constructed as described in the
		    	summary.
		
		Raises:
		    ValueError: One of three possibilities: `agent` is not given,
		    	and the certificate for the public key in `p` cannot be found
		    	in the `certs` directory; or, `agent` is not given, and `p` is
		    	not a `sign` formula; or, the private key needed to sign
		    	the credential, either inferred from `p` or corresponding to
		    	the given `agent` string, cannot be found in the
		    	`private_keys` directory.
		"""
		match p:
			case App(Operator.SIGN, 2, [q, k]):
				for cert in glob('certs/*.cert'):
					ag = Agent(f'#{cert.split("/")[1].split(".")[0]}')
					cert = Certificate.load_certificate(ag)
					if fingerprint(cert.public_key) == k.fingerprint:
						agent = cert.agent
				if agent is None:
					raise ValueError(f'could not find certificate for key {k.fingerprint}')
				p = q
			case _:
				if agent is None:
					raise ValueError(f'agent must be specified to sign {stringify(p)}')

		try:
			key = load_private_key(agent)
		except FileNotFoundError:
			raise ValueError(f'No private key found for {stringify(agent)}')
		sig = key.sign(stringify(p).encode('utf-8')).hex()
		
		return cls(p, agent, sig)

	@classmethod
	def load_credential(cls, path: str):
		with open(path, 'r') as f:
			return Credential.from_json(f.read())

	def verify_signature(self, pk: Key=None) -> bool:
		if pk is None:
			key = Certificate.load_certificate(self.signator).public_key
		else:
			key = pk
		try:
			key.verify(
				bytes.fromhex(self.signature),
				stringify(self.p).encode('utf-8')
			)
		except InvalidSignature:
			return False
		return True

	def sign_formula(self, cert: Certificate=None) -> Formula:
		"""
		Produces a representation of the credential as a `sign` formula.
		
		Returns:
			Formula: A formula `sign(self.p, [sk_self.signator])`.
		"""
		if cert is None:
			cert = Certificate.load_certificate(self.signator)
		key = fingerprint(cert.public_key)
		return parse(f'sign({stringify(self.p)}, {key})')

	def __str__(self):
		digest = hashlib.md5(bytes.fromhex(self.signature)).hexdigest()
		return (
			f"{'*'*35} Credential {'*'*35}\n"
			f"statement: {stringify(self.p)}\n"
			f"signator: {stringify(self.signator)}\n"
			f"signature: [{':'.join(a+b for a,b in zip(digest[::2], digest[1::2]))}]\n"
			f"{'*'*82}\n"
		)

@dataclass(eq=True, frozen=True)
class Certificate():

	"""
	Constructor for certificate objects. Certificates associate
	public keys to agents, and are (typically) signed by
	certificate authorities.

	Args:
		public_key (Ed25519PublicKey): A public key
		agent (Agent): The agent who owns the private key
			corresponding to `public_key`.
		cred (Credential): A credential, presumably signed by a
			certificate authority, which states 
			`iskey(public_key, agent)`.
	"""
	
	public_key: Ed25519PublicKey
	agent: Agent
	cred: Credential

	def serialize(self) -> str:
		return json.dumps(
			{
				'public_key': self.public_key.public_bytes(
					Encoding.PEM, 
					PublicFormat.SubjectPublicKeyInfo
				).hex(),
				'agent': self.agent.id,
				'cred': json.loads(self.cred.serialize())
			},
			sort_keys=True,
			indent=2
		)

	@classmethod
	def from_json(cls, ser: str):
		ob = json.loads(ser)
		return cls(
			load_pem_public_key(bytes.fromhex(ob['public_key'])),
			Agent(ob['agent']), 
			Credential.from_json(json.dumps(ob['cred']))
		)

	@classmethod
	def load_certificate(cls, user: Agent):
		"""
		Load the certificate for `user` from the `certs` 
		directory of the repository.
		
		Args:
		    user (Agent): User whose certificate to load.
		
		Returns:
		    Certificate: The deserialized object loaded from
		    	`certs/user.cert`.
		"""
		filename = f'certs/{user.id[1:]}.cert'
		with open(filename, 'r') as f:
			return cls.from_json(f.read())

	@classmethod
	def make_for_key(
		cls,
		public_key: Ed25519PublicKey,
		agent: Agent,
		signator: Agent
	) -> Certificate:
		"""
		Construct a certificate object for a freshly-generated
		key, to be associated with a given agent, with an
		`iskey(pk, agent)` credential signed by the given
		signator.
		
		Args:
		    public_key (Ed25519PublicKey): The public key to certify.
		    agent (Agent): The agent who should be associated with
		    	`public_key`.
		    signator (Agent): The agent whose private key will be used
		    	to sign the certificate. The agent's private key must
		    	be present in the `private_keys` directory.

		   Returns:
		   	Certificate: The new certificate described in the summary.
		"""
		cred = Credential.from_formula(
			parse(f'iskey({agent.id}, {fingerprint(public_key)})'), signator
		)
		return Certificate(public_key, agent, cred)

	def __str__(self):
		return (
			f"{'='*29} Public Key Certificate {'='*29}\n"
			f"key: {fingerprint(self.public_key)}\n"
			f"agent: {stringify(self.agent)}\n"
			f"{str(self.cred)}"
			f"{'='*82}\n"
		)

@dataclass(eq=True, frozen=True)
class AccessRequest():

	"""
	Constructor for access request objects. Access requests specify
	a claim that some agent, typically one with the appropriate authority
	to make access control decisions (e.g., `#root`), is willing to grant
	a user access to a particular resource. In other words, the request
	is a statement of the form `A says open(B, R)`, where `A` has the
	authority to grant access to resource `R`.

	Access requests are signed by an agent who makes the request, and
	provide a proof of the request along with the credentials and certificates
	needed to establish any assumptions made by the proof. For example,
	agent `#aditi` might make the request `#root says open(#aditi, <sol.txt>)`.
	Her proof of this formula might depend on a credential issued by
	`#mfredrik` stating that she has permission to open the resource,
	a policy credential issued by `#root` which says that `#mfredrik` can 
	delegate access to `<sol.txt>`, and the certificates of `#mfredrik`,
	`#root`, and `#ca`, as the latter was used to sign the former certificates.

	Args:
		proof (Proof): A proof of the access request.
		signature (Credential): A credential representing a signature
			of the access request, signed by the agent making the
			request.
		creds (set[Credential]): Any credentials needed to verify the proof.
		certs (set[Certificate]): Any certificates needed to verify the
			credentials.
	"""
	
	proof: Proof
	signature: Credential
	creds: set[Credential]
	certs: set[Certificate]

	@staticmethod
	def proof_as_dict(pf: Proof) -> dict[str, dict]:
		return {
			'premises': [AccessRequest.proof_as_dict(prem) for prem in pf.premises],
			'conclusion': stringify(pf.conclusion),
			'rule': pf.rule.name
		}

	@staticmethod
	def proof_from_dict(d: dict[str, dict]) -> Proof:
		return Proof(
			[AccessRequest.proof_from_dict(prem) for prem in d['premises']],
			sequent_parse(d['conclusion']),
			calculus[d['rule']]
		)

	def serialize(self) -> str:
		return json.dumps(
			{
				'proof': AccessRequest.proof_as_dict(self.proof),
				'signature': json.loads(self.signature.serialize()),
				'creds': [json.loads(cred.serialize()) for cred in self.creds],
				'certs': [json.loads(cert.serialize()) for cert in self.certs]
			},
			sort_keys=True,
			indent=2
		)

	@classmethod
	def from_json(cls, ser: str):
		ob = json.loads(ser)
		return cls(
			AccessRequest.proof_from_dict(ob['proof']),
			Credential.from_json(json.dumps(ob['signature'])),
			[Credential.from_json(json.dumps(cred)) for cred in ob['creds']],
			[Certificate.from_json(json.dumps(cert)) for cert in ob['certs']]
		)

	@classmethod
	def make_for_proof(
		cls, 
		pf: Proof, 
		ag: Agent, 
		creds: set[Credential], 
		certs: set[Certificate]
	):
		"""
		Generates an access request for a proof, on behalf of a
		given agent.
		
		Args:
		    pf (Proof): The proof to base the request on. The conclusion
		    	of the proof must be a sequent whose `delta` is of
		    	the form `A says open(B, R)`.
		    ag (Agent): The agent to make the request on behalf of.
		    	The agent's private key must be present in the
		    	`private_keys` directory, as it will be used to
		    	sign the request. `ag` does not necessarily need to
		    	be one of the agents mentioned in the access request
		    	formula `A says open(B, R)`; access requests can be made
		    	on behalf of agents other than the one who signed the
		    	request.
		    creds (set[Credential]): The credentials needed to
		    	verify `pf`.
		    certs (set[Certificate]): Any certificates, including
		    	certificate authorities, needed to verify `creds`.

		Returns:
			AccessRequest: The access request for `pf`; see the class summary
				for a detailed description.

		Raises:
			ValueError:
		"""
		match pf.conclusion.delta.p:
			case App(Operator.SAYS, 2, [ag1, App(Operator.OPEN, 2, [ag2, _])]):
				pass
			case _:
				raise ValueError(
					f'Invalid access goal: {stringify(pf.conclusion.delta)}'
				)
		try:
			signature = Credential.from_formula(pf.conclusion.delta.p, ag)
		except FileNotFoundError:
			raise ValueError(f'No private key found for {stringify(agent)}')

		# When the `AccessRequest` is verified, the assumptions needed to
		# prove it will be populated from the `creds` and `certs` that it
		# contains. The proof is rewritten to strip away the left side of
		# all sequents, which greatly reduces the size of the object
		# when it is serialized.
		return cls(rebase_proof(pf, []), signature, creds, certs)

	def __str__(self):
		preamble = (
			f"{'<'*36} Request {'<'*37}\n"
			f"signature:\n{self.signature}"
		)
		creds = '\ncredentials:\n'
		for cred in self.creds:
			creds = f'{creds}{cred}'
		certs = '\ncertificates:\n'
		for cert in self.certs:
			certs = f'{certs}{cert}'
		post = f"{'>'*82}"
		return preamble + creds + certs + post

def load_private_key(user: Agent) -> Ed25519PrivateKey:
	"""
	Load the private key for a given agent, e.g.,
	for the purpose of generating a signature.
	
	Args:
	    user (Agent): The agent to load; their private
	    	key must be in the `private_keys` directory.
	
	Returns:
	    Ed25519PrivateKey: A private key that can be used
	    	to construct signatures; see the implementation of
	    	`Credential.from_formula` for an example.
	"""
	filename = f'private_keys/{user.id[1:]}.pem'
	with open(filename, 'rb') as f:
		return load_pem_private_key(f.read(), password=None)


def new_user(ag: Agent, signator: Agent, save_private=True, save_cert=True) -> Certificate:
	"""
	Generate a new private key and certificate, signed by a specified agent.
	
	Args:
	    ag (Agent): User to construct
	    signator (Agent): Agent to sign new user's certificate
	    save_private (bool, optional): Save the private key to `private_keys`
	    save_cert (bool, optional): Save the certificate to `certs`
	
	Returns:
	    Certificate: Certificate for new agent `ag`, signed by `signator`
	"""
	# generate the key pair
	private_key = Ed25519PrivateKey.generate()
	public_key = private_key.public_key()

	# write the private key to disk
	if save_private:
		private_bytes = private_key.private_bytes(Encoding.PEM, PrivateFormat.PKCS8, NoEncryption())
		with open(f'private_keys/{ag.id[1:]}.pem', 'wb') as f:
			f.write(private_bytes)

	# generate the public key certificate
	if ag == signator:
		signing_key = private_key
	else:
		signing_key = load_private_key(signator)
	cert_p = parse(f'iskey({ag.id}, {fingerprint(public_key)})')
	sig = signing_key.sign(stringify(cert_p).encode('utf-8')).hex()
	cert_cred = Credential(cert_p, signator, sig)
	cert = Certificate(public_key, ag, cert_cred)

	# write the certificate to disk
	if save_cert:
		with open(f'certs/{ag.id[1:]}.cert', 'w') as f:
			f.write(cert.serialize())
			f.write('\n')

	return cert

def fingerprint(key: Ed25519PublicKey) -> str:
	key_bytes = key.public_bytes(Encoding.Raw, PublicFormat.Raw)
	digest = hashlib.md5(key_bytes).hexdigest()
	return f"[{':'.join(a+b for a,b in zip(digest[::2], digest[1::2]))}]"

def verify_cert(
	cert: Certificate,
	chain: dict[Agent, Certificate],
	roots: set[Certificate]
) -> bool:
	"""
	Verify a certificate by recursively checking the signature of
	its `public_key`, until reaching a certificate authority.
	For example, if `#A`'s certificate is signed by `#B`, and
	`#B`'s certificate is signed by `#ca`, then this first checks
	the signature on `#A`'s certificate against `#B`'s public key,
	and then checks the signature on `#B`'s certificate against
	`#CA's` public key. Because `#CA`'s certificate is self-signed,
	the recursive check ends after checking the signature on `#CA`'s
	certificate.
	
	Args:
	    cert (Certificate): The certificate to verify.
	    chain (dict[Agent, Certificate]): A dictionary associating
	    	agents to certificates, for any certificate that may
	    	be needed to verify `cert` until reaching a certificate
	    	authority.
	    roots (set[Certificate]): Description

	Returns:
		bool: `True` if all of the certificates that `cert`'s signature
			depends on can be verified, and `False` otherwise.
	"""
	match cert.cred.p:
		case App(Operator.ISKEY, 2, [cert.agent, key]):
			if fingerprint(cert.public_key) != key.fingerprint:
				return False
			signing_key = chain[cert.cred.signator].public_key
			try:
				signing_key.verify(
					bytes.fromhex(cert.cred.signature),
					stringify(cert.cred.p).encode('utf-8')
				)
			except InvalidSignature:
				return False
			if cert.cred.signator not in chain.keys():
				return False			
			if cert.agent == cert.cred.signator:
				return cert in roots if len(roots) > 0 else True
			return verify_cert(chain[cert.cred.signator], chain, roots)
		case _:
			return False

def rebase_proof(pf: Proof|Sequent, gamma: list[Judgement]) -> Proof:
	"""
	When the proof in an `AccessRequest` is verified, we can only
	use assumptions that come from `Credential` and `Certificate` objects
	whose signatures have been verified. Thus, when `AccessRequest`
	objects are created, all of the assumptions can be stripped out, and
	when they are verified, the correct assumptions must be added back
	in. This function rewrites a proof by setting the left side of all
	sequents to `gamma`.
	
	Args:
	    pf (Proof | Sequent): Proof to be rewritten.
	    gamma (list[Judgement]): Set of assumptions to use for all
	    	sequents in the proof.
	
	Returns:
	    Proof: Proof rewritten as described in the summary.
	
	Raises:
	    TypeError: The `pf` argument must either be a `Proof` or `Sequent`.
	"""
	if isinstance(pf, Proof):
		conc = rebase_proof(pf.conclusion, gamma) # Sequent(gamma, pf.conclusion.delta)
		prems = [rebase_proof(prem, gamma) for prem in pf.premises]
		return Proof(prems, conc, pf.rule)
	elif isinstance(pf, Sequent):
		new_gamma = []
		for p in pf.gamma:
			match p.p:
				case App(Operator.SIGN, n, a):
					new_gamma += [p] if p in gamma else []
				case _:
					new_gamma += [p]
		new_gamma = list(set(new_gamma) | set(gamma))
		return Sequent(new_gamma, pf.delta)

	raise TypeError(f'rebase_proof expects either Proof or Sequent, got {type(pf)}')

def verify_request(req: AccessRequest, roots: list[Agent]=[]) -> Optional[Credential]:
	"""
	Verify an access request. This is a three-step process. First
	the provided certificates are checked, followed by the
	credentials. Then the certificates and credentials are used to
	construct a set of assumptions to rebase the authorization proof with
	before verifying that all branches close.
	
	Args:
		req (AccessRequest): The request
		roots (list[Agent]): A list of trusted certificate authorities to use when
			verifying certificates in the access request
	
	Returns:
		Optional[Credential]: `None` if any credential or certificate in the request
			cannot be verified, or if the proof cannot be verified using the provided
			credentials and certificates as context. Otherwise, a credential signed by
			#root containing the access request.
	"""
	# First verify all of the certificates sent with the request
	cert_chain = {cert.agent: cert for cert in req.certs}
	for cert in req.certs:
		if not verify_cert(cert, cert_chain, roots):
			return None
	# Then verify the signatures on each of the credentials
	for cred in req.creds:
		if not cred.verify_signature(cert_chain[cred.signator].public_key):
			return None

	# Now check the proof
	# First construct the sequent context from the credentials and certificates
	cas = get_cas(req.proof.conclusion)
	gamma = [Proposition(parse(f'ca({ca.id})')) for ca in cas]
	gamma += [
		Proposition(parse(f'iskey({ca.id}, {fingerprint(cert_chain[ca].public_key)})'))
		for ca in cas
	]
	gamma += [Proposition(cert.cred.sign_formula(cert_chain[cert.cred.signator])) for cert in req.certs]
	gamma += [Proposition(cred.sign_formula(cert_chain[cred.signator])) for cred in req.creds]

	# Reformulate the proof using only this context
	pf = rebase_proof(
		Proof(
			req.proof.premises, 
			Sequent(gamma, req.proof.conclusion.delta), 
			req.proof.rule), 
		gamma
	)

	# Finally, verify the proof
	if len(verify(pf, feedback=False)) > 0:
		return None

	# If we've gotten this far, everything checks out
	return Credential.from_formula(req.signature.p.args[1], Agent('#root'))
