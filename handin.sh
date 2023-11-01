#!/bin/bash

if test -f "handin.zip"; then
	rm handin.zip
fi
zip -r handin.zip . -x .git/**\* -x .git\* -x src/__pycache__/**\* -x src/__pycache__\* -x credentials\* -x creds/**\* -x certs\* -x certs/**\* -x private_keys\* -x private_keys/**\*