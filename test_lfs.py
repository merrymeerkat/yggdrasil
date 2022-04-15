import errno
from lfs import LFS
from disk import assertion, debug, Stat

from yggdrasil.diskspec import *
from yggdrasil import test

#InoSort = BitVecSort(32)
InoSort = BitVecSort(64)
NameSort = SizeSort 

def FreshIno(name):
    return FreshBitVec(name, InoSort.size())

def FreshName(name):
    return FreshBitVec(name, NameSort.size())

class LFSSpec(object):
    def __init__(self, mach, childmap, parentmap, mode, time, typ):
        self._mach = mach
        self._childmap = childmap
        self._parentmap = parentmap
        self._mode = mode
        self._time = time
        self._typ = typ
      #  self._childmap = FreshUFunction("childmap", InoSort, NameSort, InoSort)
      #  self._parentmap = FreshUFunction("parentmap", InoSort, InoSort)
      #  self._mode = FreshUFunction("mode", InoSort, NameSort)
      #  self._time = FreshUFunction("time", InoSort, NameSort)
    #def __init__(self, mach, childmap, parentmap, modefn, mtimefn):
       

    def lookup(self, cid, parent, name):
        ino = self._childmap(parent, name)
        return If(0 < ino, ino, -errno.ENOENT)

    def get_attr(self, ino):
        return Stat(size=0,
                    mode=self._mode(ino),
                    mtime=self._time(ino),
                    typ=self._typ(ino))

    def mknod(self, parent, name, mode, time, typ):
        if 0 < self.lookup(parent, name):
            #return BitVecVal(-errno.EEXIST, 32)
            return BitVecVal(-errno.EEXIST, 64)

        on = self._mach.create_on([])

        ino = FreshBitVec('ino', 64)
        #ino = FreshBitVec('ino', 32)
        assertion(0 < ino)
        assertion(Not(0 < self._parentmap(ino)))

        # QUESTION: Why is this not in a transaction?
        self._childmap = self._childmap.update((parent, name), ino, guard = on)
        self._parentmap = self._parentmap.update(ino, parent, guard = on)
        self._time = self._time.update(ino, time, guard = on)
        self._mode = self._mode.update(ino, mode, guard = on)
        self._typ = self._mode.update(ino, typ, guard = on)

        return ino

    def crash(self, mach):
        return self.__class__(mach, self._childmap, self._parentmap, self._mode, self._time, self._typ)
        #return self.__class__(mach)


class LFSRefinement(test.RefinementTest):
    def create_spec(self, mach):
        childmap =  FreshUFunction('dirfn', InoSort, SizeSort, InoSort)
        parentmap =  FreshUFunction('parentfn', InoSort, InoSort)
        modefn =  FreshUFunction('modefn', InoSort, NameSort)
        mtimefn =  FreshUFunction('mtimefn', InoSort, NameSort)
        typfn =  FreshUFunction('typfn', InoSort, NameSort)
        return LFSSpec(mach, childmap, parentmap, modefn, mtimefn, typfn)
     #   childmap = FreshUFunction("childmap", SizeSort, SizeSort, SizeSort)
     #   parentmap = FreshUFunction("parentmap", SizeSort, SizeSort)
     #   mode = FreshUFunction("mode", SizeSort, SizeSort)
     #   time = FreshUFunction("time", SizeSort, SizeSort)
     #   return LFSSpec(mach, childmap, parentmap, mode, time)

    def create_impl(self, mach):
        array = FreshDiskArray('disk')
        disk = AsyncDisk(mach, array)
        return LFS(disk)

    def pre_post(self, spec, impl, **kwargs):
        name = FreshBitVec('name.pre', 64)
        parent = BitVecVal(1, 64)
        #parent = FreshIno("parent.pre")

        sb = impl._disk.read(0)
        imap = impl._disk.read(sb[2])
        off = FreshBitVec('off', 9)

        
        pre = ForAll([name], Implies(name != 0, And(
            Implies(0 < spec._childmap(parent, name),
                parent == spec._parentmap(spec._childmap(parent, name))),

            Implies(0 < impl.lookup(parent, name),
                And(impl.lookup(parent, name) < sb[1],
                    spec.get_attr(spec.lookup(parent, name)) == impl.get_attr(impl.lookup(parent, name)))),
            spec.lookup(parent, name) == impl.lookup(parent, name))))

        pre = And(pre,
                #ForAll([off], Implies(ZeroExt(32 - off.size(), off) < sb[1], And(0 < imap[off], imap[off] < sb[0]))))
                ForAll([off], Implies(ZeroExt(64 - off.size(), off) < sb[1], And(0 < imap[off], imap[off] < sb[0]))))

        pre = And(pre,
                # allocated blocks are in range ]0..allocator[
                0 < sb[2], sb[2] < sb[0],
                0 < imap[1], imap[1] < sb[0],

                # root dir inode has been allocated
                1 < sb[1],
                )

        # Changed (added a wildcard since inodes have 5 attributes now)
        (spec, impl, (_, name0, _, _, _), (sino, iino)) = yield pre

        self.show(pre)

        if iino < 0:
            iino = impl.lookup(parent, name0)

        if self._solve(sino == iino):
            assertion(sino == iino)

        sb = impl._disk.read(0)
        imap = impl._disk.read(sb[2])

        post = ForAll([name], Implies(name != 0, And(
            Implies(0 < spec._childmap(parent, name),
                parent == spec._parentmap(spec._childmap(parent, name))),

            Implies(0 < impl.lookup(parent, name),
                And(impl.lookup(parent, name) < sb[1],
                    spec.get_attr(spec.lookup(parent, name)) == impl.get_attr(impl.lookup(parent, name)))),
            spec.lookup(parent, name) == impl.lookup(parent, name))))

        post = And(post,
                #ForAll([off], Implies(ZeroExt(32 - off.size(), off) < sb[1], And(0 < imap[off], imap[off] < sb[0]))))
                ForAll([off], Implies(ZeroExt(64 - off.size(), off) < sb[1], And(0 < imap[off], imap[off] < sb[0]))))
                

        post = And(post,
                # allocated blocks are in range ]0..allocator[
                0 < sb[2], sb[2] < sb[0],
                0 < imap[1], imap[1] < sb[0],

                # root dir inode has been allocated
                1 < sb[1],
                )

        yield post

    def match_mknod(self):
        parent = BitVecVal(1, 64)
        #parent = BitVecVal(1, 32)
        name = FreshBitVec('name', 64)
        mode = FreshBitVec('mode', 64)
        time = FreshBitVec('mtime', 64)
        typ = FreshBitVec('typ', 64)
        assertion(name != 0)
        yield (parent, name, mode, time, typ)

    # test

    # def test_foo(self):
    #     mach = Machine()
    #     impl = self.create_impl(mach)
    #
    #     parent = BitVecVal(1, 64)
    #     name = BitVecVal(0xdeadbeef, 64)
    #     mode = BitVecVal(0x1337, 64)
    #
    #     sb = impl._disk.read(0)
    #     imap = impl._disk.read(sb[2])
    #
    #     name0 = FreshSize('name')
    #
    #     pre = And(
    #             # inode alloc
    #             0 < sb[1], sb[1] < 512,
    #
    #             # allocated blocks are in range ]0..allocator[
    #             0 < sb[2], sb[2] < sb[0],
    #             0 < imap[1], imap[1] < sb[0],
    #             0 < imap[1], sb[2] < imap[1],
    #
    #             # root dir inode has been allocated
    #             1 < sb[1],
    #
    #             ForAll([name0],
    #                 Implies(0 < impl.lookup(parent, name0),
    #                     And(
    #                         impl.lookup(parent, name0) < sb[1],
    #                         imap[Extract(8, 0, impl.lookup(parent, name0))] < sb[0]))))
    #
    #     res = impl.mknod(parent, name, mode)
    #     if res < 0:
    #         pass
    #     else:
    #         ino = impl.lookup(parent, name)
    #         v = impl.get_attr(ino)
            # self.psolve(pre, v != mode)




if __name__ == '__main__':
    test.main()
