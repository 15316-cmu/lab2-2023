USE_REDIS = True

if USE_REDIS:
    from .redis_backend import (initialize_global_database, get, set)
else:
    from .inmemory_backend import (initialize_global_database, get, set)


async def validate_andrewid(andrewid: str) -> bool:
    """
    Looks to see if andrewid is present in the database
    """
    return await get(andrewid) is not None


async def add_andrewid(andrewid: str):
    """
    Add a given andrewid to the database
    """
    return await set(andrewid, "1")


async def record_completion(andrewid: str,
                            submission: str):
    """
    Records completion of a task
    """
    return await set(f"{andrewid}", submission)


TASKS = {"task1": 10}


async def get_score(andrewid: str):
    """
    Computes the score of a student based on all the tasks they have submitted"
    """
    student_score = 0
    total_score = 0

    for task_name, task_score in TASKS.items():
        if await get(f"{andrewid}-{task_name}") is not None:
            student_score += task_score
        total_score += task_score

    return student_score / total_score


if __name__ == "__main__":
    # Add local andrewid to database for convenience
    import asyncio

    from sanic import Sanic

    app = Sanic.get_app("lab2", force_create=True)

    # Modify this to be your andrewid
    app.config.ANDREWID = "testid"
    app.config.DATABASE = "redis://localhost/0"

    async def run():
        await initialize_global_database(None, None)
        await add_andrewid(ANDREWID)
        print(f"Added {ANDREWID} to the database")

    asyncio.run(run())
