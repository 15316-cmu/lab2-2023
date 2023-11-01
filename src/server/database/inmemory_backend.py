from typing import Optional

from sanic import Sanic

app = Sanic.get_app("lab2", force_create=True)


async def initialize_global_database(_app, _loop):
    app.ctx.db = {app.config.ANDREWID: "1"}


async def get(key: str) -> Optional[str]:
    return app.ctx.db.get(key)


async def set(key: str, value: str):
    app.ctx.db[key] = value
