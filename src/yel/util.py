from __future__ import annotations

import collections

from .constants import *

import os
import tempfile as tmp
from contextlib import contextmanager

@contextmanager
def tempfile(suffix='', dir=None):
    """ Context for temporary file.

    Will find a free temporary filename upon entering
    and will try to delete the file on leaving, even in case of an exception.

    Parameters
    ----------
    suffix : string
        optional file suffix
    dir : string
        optional directory to save temporary file in
    """

    tf = tmp.NamedTemporaryFile(delete=False, suffix=suffix, dir=dir)
    tf.file.close()
    try:
        yield tf.name
    finally:
        try:
            os.remove(tf.name)
        except OSError as e:
            if e.errno == 2:
                pass
            else:
                raise

@contextmanager
def open_atomic(filepath, *args, **kwargs):
    """ Open temporary file object that atomically moves to destination upon
    exiting.

    Allows reading and writing to and from the same filename.

    The file will not be moved to destination in case of an exception.

    Parameters
    ----------
    filepath : string
        the file path to be opened
    fsync : bool
        whether to force write the file to disk
    *args : mixed
        Any valid arguments for :code:`open`
    **kwargs : mixed
        Any valid keyword arguments for :code:`open`
    """
    fsync = kwargs.pop('fsync', False)

    with tempfile(dir=os.path.dirname(os.path.abspath(filepath))) as tmppath:
        with open(tmppath, *args, **kwargs) as file:
            try:
                yield file
            finally:
                if fsync:
                    file.flush()
                    os.fsync(file.fileno())
        os.rename(tmppath, filepath)

class FwdDict(py.dict, collections.UserDict):
    def __init__(self, dict=None, /, **kwargs):
        super().__init__()
        # super().__init__(dict, **kwargs)
        # collections.UserDict.__init__(self, dict, **kwargs)
        # super(self, collections.UserDict).__init__(dict, **kwargs)
        self.data = {}
        if dict is not None:
            self.update(dict)
        if kwargs:
            self.update(kwargs)


    # def __setitem__(self, __k: KT, __v: VT) -> None:
    #     pass
    #
    # def __delitem__(self, __v: KT) -> None:
    #     pass
    #
    # def __getitem__(self, __k: KT) -> VT_co:
    #     pass
    #
    # def __len__(self) -> int:
    #     pass
    #
    # def __iter__(self) -> Iterator[T_co]:
    #     pass

    def __len__(self):
        return len(self.data)

    def __getitem__(self, key):
        if key in self.data:
            return self.data[key]
        if hasattr(self.__class__, "__missing__"):
            return self.__class__.__missing__(self, key)
        raise KeyError(key)

    def __setitem__(self, key, item):
        self.data[key] = item

    def __delitem__(self, key):
        del self.data[key]

    def __iter__(self):
        return iter(self.data)

    # Modify __contains__ to work correctly when __missing__ is present
    def __contains__(self, key):
        return key in self.data

    # Now, add the methods in dicts but not in MutableMapping
    def __repr__(self):
        return repr(self.data)

    def __or__(self, other):
        if isinstance(other, FwdDict):
            return self.__class__(self.data | other.data)
        if isinstance(other, dict):
            return self.__class__(self.data | other)
        return NotImplemented

    def __ror__(self, other):
        if isinstance(other, FwdDict):
            return self.__class__(other.data | self.data)
        if isinstance(other, dict):
            return self.__class__(other | self.data)
        return NotImplemented

    def __ior__(self, other):
        if isinstance(other, FwdDict):
            self.data |= other.data
        else:
            self.data |= other
        return self

    def __copy__(self):
        inst = self.__class__.__new__(self.__class__)
        inst.__dict__.update(self.__dict__)
        # Create a copy and avoid triggering descriptors
        inst.__dict__["data"] = self.__dict__["data"].copy()
        return inst

    def copy(self):
        if self.__class__ is FwdDict:
            return FwdDict(self.data.copy())
        import copy
        data = self.data
        try:
            self.data = {}
            c = copy.copy(self)
        finally:
            self.data = data
        c.update(self)
        return c

    @classmethod
    def fromkeys(cls, iterable, value=None):
        d = cls()
        for key in iterable:
            d[key] = value
        return d

