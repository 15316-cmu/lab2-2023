from sanic import response, HTTPResponse
from typing import Optional, Tuple


def get_fields(data: dict, fields: Tuple[str, ...]) -> Optional[Tuple[str, ...]]:
    """
    Returns: None is data is missing any of fields, Some(tuple) containng the
    extracted data otherwise
    """

    output = tuple(map(lambda field: data.get(field, None), fields))

    if any(value is None for value in output):
        return None
    else:
        return output


def error_response(message: str, http_code=400) -> HTTPResponse:
    """
    Returns a formatted JSON response object signifying an error
    """
    return response.json({"error": message}, status=http_code)


def correct_response(data: dict, http_code=200) -> HTTPResponse:
    """
    Returns a formatted JSON response object signifying correct execution
    """
    return response.json(data, status=http_code)
