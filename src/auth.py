#!/usr/bin/env python3

from __future__ import annotations

import json
from glob import glob
from urllib.request import Request, urlopen
from urllib.parse import urlencode
from urllib.error import HTTPError

from logic import *
from prover import prove
from util import stringify
from parser import parse
from crypto import (
    AccessRequest,
    Certificate,
    Credential,
    fingerprint,
    verify_request
)


def sequent_context(creds: set[Credential]) -> list[Judgement]:
	"""
	Produces a list of judgements from a set of `Credential`
	objects. A credential of formula `P` signed by agent `A` will
	produce a judgement `sign(P, [pk_A]) true`. 
	
	Args:
	    creds (set[Credential]): Set of credentials to add to the
	    	context.
	
	Returns:
	    list[Judgement]: Sequent context described above
	"""
	ca_key = Certificate.load_certificate(Agent('#ca'))
	ca = [
		Proposition(parse('ca(#ca)')), 
		Proposition(parse(f'iskey(#ca, {fingerprint(ca_key.public_key)})'))
	]
	iskeys = []
	props = []
	for cred in creds:
		cert = Certificate.load_certificate(cred.signator)
		key = fingerprint(cert.public_key)
		signing_cert = Certificate.load_certificate(cert.cred.signator)
		signing_key = fingerprint(signing_cert.public_key)
		prop = Proposition(parse(f'sign(iskey({cred.signator.id}, {key}), {signing_key})'))
		if not prop in iskeys:
			iskeys.append(prop)
		prop = Proposition(cred.sign_formula())
		if not prop in props:
			props.append(prop)
	return ca + iskeys + props

def load_all_creds() -> list[Judgement]:
	"""
	Create a sequent context (list of judgements) by loading all of
	the credentials in the `credentials` directory of the repository.
	
	Returns:
	    list[Judgement]: List constructed by calling `sequent_context` on
	    	each loaded credential.
	"""
	creds = [Credential.load_credential(cred) for cred in glob('credentials/*.cred')]
	return sequent_context(creds)

def gather_credentials(ob: Proof|Sequent|Formula) -> set[Formula]:
	"""
	Collects all of the credentials appearing in a `Proof`, `Sequent`, or
	`Formula` object. In this context, a credential is a formula of the
	form `sign(P, [pk])`.
	
	Args:
	    ob (Proof | Sequent | Formula): Object to collect from.
	
	Returns:
	    set[Formula]: If the object is a `Proof`, then all of the credentials
	    in the goal (`delta`) of the conclusion sequent, and recursively all
	    credentials in the premises; if a `Sequent`, then the credentials in
	    `ob.delta`; if a `Formula`, then any `sign` formula appearing within.
	"""
	match ob:
		case Proof(prems, conclusion, _):
			return gather_credentials(conclusion).union(*[gather_credentials(prem) for prem in prems])
		case Sequent(_, delta):
			return gather_credentials(delta.p)
		case App(Operator.SIGN, _, _):
			return set([ob])
		case App(_, _, args):
			return set([]).union(*[gather_credentials(arg) for arg in args])
		case _:
			return set([])

def gather_cas(ob: Proof|Sequent|Formula) -> set[Agent]:
	"""
	Collects all agents `A` appearing in `ca(A)` formulas
	within the object.
	
	Args:
	    ob (Proof | Sequent | Formula): Object to collect from.
	
	Returns:
	    set[Agent]: The set of agents described in the summary.
	"""
	match ob:
		case Proof(prems, conclusion, _):
			return gather_cas(conclusion).union(*[gather_cas(prem) for prem in prems])
		case Sequent(gamma, delta):
			return gather_cas(delta.p).union(*[gather_cas(p.p) for p in gamma])
		case App(Operator.ISCA, 1, [ca]):
			return set([ca])
		case App(_, _, args):
			return set([]).union(*[gather_cas(arg) for arg in args])
		case _:
			return set([])

def generate_request(pf: Proof, ag: Agent) -> AccessRequest:
	"""
	Generates an `AccessRequest` to send to the authorization server,
	signed with the secret key of the specified agent.
	
	Args:
	    pf (Proof): Authorization proof of a goal `open(#A, <R>)`, for
	    	some agent `#A` and resource `<R>`.	    
	    ag (Agent): The agent to generate the request on behalf of.
	    	The agent's private key must exist in the `private_keys`
	    	directory at the root of the repository.
	
	Returns:
	    AccessRequest: A request generated by calling `gather_credentials`
	    	and `gather_cas` on `pf`, and signing the request with
	    	`ag`'s private key.
	"""
	cas = gather_cas(pf)
	signs = gather_credentials(pf)
	cert_creds = [
		sg.args[0].args[0] 
		for sg in signs 
		if isinstance(sg.args[0], App) and sg.args[0].op == Operator.ISKEY
	]
	policy_creds = [
		sg
		for sg in signs 
		if not(isinstance(sg.args[0], App) and sg.args[0].op == Operator.ISKEY)
	]
	certs = [Certificate.load_certificate(ca) for ca in cas | set([ag]) | set(cert_creds)]
	creds = [Credential.load_credential(cred) for cred in glob('credentials/*.cred')]
	all_creds = {cred.sign_formula(): cred for cred in creds}
	creds = [all_creds[cred] for cred in policy_creds]
	return AccessRequest.make_for_proof(pf, ag, creds, certs)

if __name__ == '__main__':
	import sys
	import argparse

	argparser = argparse.ArgumentParser(
		prog = 'auth.py',
		description = (
			'Constructs an authorization request, with proof.\n'
			'Optionally sends the request to the authorization server.'
		),
	)
	argparser.add_argument(
		'requester',
		help='agent making the request (use your andrew id)'
	)
	argparser.add_argument(
		'resource',
		help='resource under request (either shared.txt or secret.txt)'
	)
	argparser.add_argument(
		'-s', '--send_request',
		action='store_true',
		help='send the request to the authorization server'
	)
	args = argparser.parse_args()
	
	agent = Agent(f'#{args.requester}')
	res = Resource(f'<{args.resource}>')
	do_send = args.send_request

	goal = Proposition(parse(f'#root says open({agent.id}, {res.id})'))
	seq = Sequent(load_all_creds(), goal)
	pf = prove(seq)

	if pf is None:
		print('could not find authorization proof')
	else:
		req = generate_request(pf, agent)

		if args.send_request:

			print('sending to authorization server:')
			print(req)
			request = Request("http://authproof.net:15316/accessrequest",
							  data=urlencode({
								  "request": req.serialize()
							  }).encode('utf-8'),
							  method='POST')
			try:
				response_object = urlopen(request, timeout=100)
			except HTTPError as e:
				response_object = e

			resp_json = json.load(response_object)
			print('\nserver response:')
			try:
				new_cred = Credential.from_json(resp_json)
				print(new_cred)
			except:
				print(resp_json)
		else:
			print('\ngenerated request:')
			print(req)
			print('\n\nuse the `-s` flag to send this to the server')