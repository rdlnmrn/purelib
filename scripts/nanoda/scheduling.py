"""Check ready complete streams concurrently while other exports are running."""

from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait


def schedule(groups, export, check, *, exporters, checkers, cancel, pipeline=True):
    """Run bounded independent pools, cancelling both on any failure or interruption."""
    if exporters < 1 or checkers < 1 or not groups:
        raise ValueError('nonempty groups and positive worker counts are required')
    producers = ThreadPoolExecutor(max_workers=exporters)
    consumers = ThreadPoolExecutor(max_workers=checkers)
    pending = {}
    exported, checked = {}, {}
    try:
        for index, group in enumerate(groups):
            pending[producers.submit(export, group)] = 'export', index
        while pending:
            finished, _ = wait(pending, return_when=FIRST_COMPLETED)
            for future in finished:
                role, index = pending.pop(future)
                value = future.result()
                if role == 'export':
                    exported[index] = value
                    if pipeline:
                        pending[consumers.submit(check, value)] = 'check', index
                else:
                    checked[index] = value
        if not pipeline:
            pending = {consumers.submit(check, exported[index]): ('check', index)
                       for index in range(len(groups))}
            while pending:
                finished, _ = wait(pending, return_when=FIRST_COMPLETED)
                for future in finished:
                    _, index = pending.pop(future)
                    checked[index] = future.result()
        if set(exported) != set(checked) or len(checked) != len(groups):
            raise ValueError('pipeline did not independently check every exported group')
        return [(exported[index], checked[index]) for index in range(len(groups))]
    except BaseException:
        cancel()
        for future in pending:
            future.cancel()
        raise
    finally:
        producers.shutdown(wait=True, cancel_futures=True)
        consumers.shutdown(wait=True, cancel_futures=True)
