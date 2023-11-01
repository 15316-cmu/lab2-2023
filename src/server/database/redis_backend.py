#!/usr/bin/env python3

from typing import Optional

from redis import asyncio as aioredis
from sanic import Sanic

app = Sanic.get_app("lab2", force_create=True)


async def initialize_global_database(_app, _loop):
    app.ctx.db = await aioredis.from_url(app.config.DATABASE)


async def get(key: str) -> Optional[str]:
    return await app.ctx.db.get(key)


async def set(key: str, value: str):
    return await app.ctx.db.set(key, value)
