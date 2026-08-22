"""Check bytes resolved by an entirely Python-defined CAS."""

from covalence.cas import CasNotFoundError, get_checked
from covalence.lib.hash import O256


class DictCas:
    """The provider owns plain bytes and may implement any userspace policy."""

    def __init__(self, blobs: dict[O256, bytes]) -> None:
        self._blobs = blobs

    def get(self, address: O256) -> bytes:
        try:
            blob = self._blobs[address]
        except KeyError as error:
            raise CasNotFoundError(str(address)) from error

        return blob


payload = b"arbitrary Python CAS logic"
expected = O256.hash(payload)
provider = DictCas({expected: payload})
fact = get_checked(provider, expected)

assert fact.hash == expected
assert fact.blob == payload
print(f"resolved {fact.hash} ({len(fact.blob)} bytes)")
