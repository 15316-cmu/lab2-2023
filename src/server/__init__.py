import argparse
import functools
import logging
import os
import sys
from typing import Awaitable, Callable, Optional

from sanic import HTTPResponse, Request, Sanic, response
app = Sanic("lab2")
log = logging.getLogger(__name__)

from crypto import AccessRequest, verify_request
from logic import Agent

from .database import (initialize_global_database, record_completion,
                       validate_andrewid)
from .util import correct_response, error_response, get_fields

PROJECT_ROOT = os.path.dirname(os.path.abspath(__file__))


def task_handler(
    task_checker: Callable[[AccessRequest], Optional[str]], 
    task_recorder: Callable[[str, str], Awaitable[None]]
) -> Callable[[Request], Awaitable[HTTPResponse]]:
    """
    Given a proof checker, create a handler that will run task_checker on the
    proof received from the network, and call task_recorder with their given
    andrewid and proof
    """

    async def _task_handler(request):
        if (data := get_fields(request.form, (
                "request",
        ))) is None:
            return error_response("Missing `request` field on submission!")

        request_serialized = data[0]
        request = AccessRequest.from_json(request_serialized)
        andrewid = request.signature.signator.id

        if not request.signature.verify_signature():
            return error_response("invalid request signature for user {andrewid.id}")

        # call `verify_request` on the user's request
        resp = task_checker(request)
        await task_recorder(andrewid, request_serialized)
        if resp is None:
            return error_response("That doesn't look right to me...")
        else:
            return correct_response(resp.serialize())

    return _task_handler


def make_parser():
    """
    CLI argument definitions
    """
    parser = argparse.ArgumentParser(description="Start the lab2 server")
    parser.add_argument('--host',
                        type=str,
                        default="0.0.0.0",
                        help="Network address to bind to")
    parser.add_argument('--port',
                        type=int,
                        default=15316,
                        help="Port to bind to")
    parser.add_argument('--num_workers',
                        type=int,
                        default=1,
                        help="How many threads to run the server in")
    parser.add_argument('--release',
                        action="store_true",
                        help="Run the server in release mode")

    return parser


def main():
    args = make_parser().parse_args()

    # When clients connect using auth.py, the server will call
    # `verify_request` (from crypto.py) on the `AccessRequest`
    # object that they send
    app.add_route(task_handler(verify_request, record_completion),
                  '/accessrequest',
                  methods=['POST'])

    app.config.DATABASE = "redis://localhost/0"
    app.main_process_start(initialize_global_database)

    app.run(host=args.host,
            port=args.port,
            workers=args.num_workers,
            debug=not args.release)


if __name__ == "__main__":
    main()
