from ast import parse, unparse, FunctionDef, ClassDef, AnnAssign, Assign, expr, Name, iter_child_nodes, AST, fix_missing_locations, NodeTransformer, Import, ImportFrom, literal_eval, Constant, Call, Load
from functools import cache, reduce
from itertools import chain
from random import sample
from subprocess import run, CompletedProcess
from time import perf_counter
from multiprocessing import Pool, cpu_count
from datetime import datetime
from json import dump
from builtins import __dict__ as btn_dict
from multiprocessing import Value, Lock
from time import sleep
import zlib

import tempfile
import atexit
import os

import tempfile
import atexit
import os
import shutil


def is_builtin_class_name(name: str) -> bool:
    return name in btn_dict and isinstance(btn_dict[name], type)


TIME = False
TOP_LEVEL = (None, None)
GuideKey = tuple[str | None, str | None]
GuideType = dict[GuideKey, bool]

class Timer:
    def __init__(self, name):
        self.name = name
        self.start = perf_counter() if TIME else None

    def end(self):
        if TIME:
            dt = perf_counter() - self.start
            print(f"{self.name}: {dt:.6f}s")




# we need all this to make the loading bar work
_g_counter = None
_g_lock = None

def _init_worker(counter, lock):
    global _g_counter, _g_lock
    _g_counter = counter
    _g_lock = lock

def run_perm_worker(args):
    me, perm = args
    stderr = me.run_permutation(perm)
    global _g_counter, _g_lock
    with _g_lock:
        _g_counter.value += 1
    return CinderDetyper._perm_name(perm), stderr

class CinderDetyper:
    def __init__(self, runner_file_name: str, python: str, scratch_dir: str, params: tuple[str] = ()):
        t1 = Timer("init")
        self.params = params
        self.python = python
        self.runner_file_name = runner_file_name
        self.lib_file_name = f"{CinderDetyper.file_trunc(runner_file_name)}_lib.py"
        self.scratch_dir = scratch_dir
        t2 = Timer("neumerate")
        self.class_antrs, self.fun_names = self._enumerate_funs()
        t2.end()
        t1.end()

    def fun_count(self):
        return len(self.fun_names)

    @staticmethod
    @cache
    def read_text(file_name):
        with open(file_name, encoding = "utf-8") as f:
            return f.read()
        raise RuntimeError("python file not found")

    @cache
    def _read_lib_ast(self):
        return parse(CinderDetyper.read_text(self.lib_file_name), type_comments = True)

    @cache
    def _read_runner_ast(self):
        return parse(CinderDetyper.read_text(self.runner_file_name), type_comments = True)


    def _enumerate_funs(self):
        # initialized with top level already present
        q_fun_names = {TOP_LEVEL}
        antr_graph = {None: set()}

        # NO ONE should be using any of these except _enumerate_funs
        def antr_classes(anter_exprs: list[expr]):
            assert all(isinstance(a, Name) for a in anter_exprs), "only simple inheritance supported"
            # antr_names = tuple(a.id for a in anter_exprs if not is_builtin_class_name(a.id))
            # TODO: fix this assert by checking imports and stuff
            # assert all(antr_name in antr_graph for antr_name in antr_names), f"out of order inheritance not supported: {antr_names} {antr_graph}"

            # direct bases
            antr_names = tuple(a.id for a in anter_exprs if a.id in antr_graph)
            anter_set: set[str] = set(antr_names)
            antr_name_sets = tuple(set(antr_graph[antr_name]) for antr_name in antr_names)
            return reduce(lambda a, b: a.union(b), antr_name_sets, anter_set)

        def update_antr_graph(class_node: ClassDef):
            class_name = class_node.name
            assert class_name not in antr_graph, "class name shadowing not supported"
            antr_graph[class_name] = frozenset(antr_classes(class_node.bases))

        def antr_fun_gen(fun_name: str, antr_name: str | None = None):
            assert antr_name in antr_graph, f"function somehow processed before class ancestors: {antr_name} {fun_name}\n{antr_graph}"
            anters = antr_graph[antr_name]
            yield from zip(anters, (fun_name,) * len(anters))

        def fun_exists(antr_name: str, fun_name: str):
            return (antr_name, fun_name) in q_fun_names

        def is_fun_overload(fun_name: str, antr_name: str | None = None):
            assert not fun_exists(antr_name, fun_name), "function name shadowing not supported"
            return not any(fun_exists(*q_name) for q_name in antr_fun_gen(fun_name, antr_name = antr_name))

        def count_gen(node: AST, antr_name: str | None = None, fun_name: str | None = None):
            inside_fun = fun_name != None
            inside_class = antr_name != None
            for child_node in iter_child_nodes(node):
                is_fun = isinstance(child_node, FunctionDef)
                is_class = isinstance(child_node, ClassDef)
                assert not (is_fun and inside_fun), "function inside function not supported"
                assert not (is_class and inside_fun), "class inside function not supported"
                assert not (is_class and inside_class), "class inside class not supported"
                if is_fun:
                    if is_fun_overload(child_node.name, antr_name):
                        q_fun_names.add((antr_name, child_node.name))
                        yield 1
                    else:
                        yield 0

                    # TODO: support function inside function
                    yield from count_gen(child_node, antr_name = antr_name, fun_name = child_node.name)
                elif is_class:
                    update_antr_graph(child_node)
                    yield from count_gen(child_node, antr_name = child_node.name, fun_name = fun_name)
                else:
                    yield 0

        fun_count = sum(count_gen(self._read_lib_ast())) + 1 # +1 for top level of course
        assert fun_count == len(q_fun_names), "function counting logic failure: function name count != new function count"
        return antr_graph, tuple(q_fun_names)

    def _detype_funs(self, tree: AST, guide: GuideType) -> str:

        # NO ONE should be using any of these except _detype_funs
        @cache
        def q_fun_names(fun_name: str, antr_name = None):
            assert antr_name in self.class_antrs, "class ancestor graph incomplete"
            anters = self.class_antrs[antr_name]
            anter_fun_names = tuple(q_name for q_name in zip(anters, (fun_name,) * len(anters)) if q_name in self.fun_names)
            return ((antr_name, fun_name),) + anter_fun_names

        def fun_q_name(fun_name: str, antr_name = None):
            q_fun_name, *alternate_names = q_fun_names(fun_name, antr_name = antr_name)
            assert len(alternate_names) <= 1, f"function identity failure: one of {alternate_names}"
            return alternate_names[0] if alternate_names else q_fun_name

        def fun_should_be_detyped(fun_name: str, antr_name: str | None = None):
            fun_name = fun_q_name(fun_name, antr_name = antr_name)
            assert fun_name in guide, "function type status unspecified"
            return guide[fun_name]

        def detype_fun_params(fn: FunctionDef):
            args = fn.args
            args_to_clear = chain(args.posonlyargs, args.args, args.kwonlyargs, (args.vararg, args.kwarg))
            args_to_clear_filtered = filter(bool, args_to_clear) # should null args be an error?
            for a in args_to_clear_filtered:
                a.annotation = None

        def detype_fun_ret(fn: FunctionDef):
            fn.returns = None
            fn.type_comment = None

        def detype_body(node: AST, antr_name: str | None = None, fun_name: str | None = None):
            inside_fun = fun_name is not None
            inside_class = antr_name is not None
            is_toplevel = (not inside_fun) and (not inside_class)
            for child_node in iter_child_nodes(node):
                is_fun = isinstance(child_node, FunctionDef)
                is_class = isinstance(child_node, ClassDef)
                is_assign = isinstance(child_node, Assign)
                is_annassign = isinstance(child_node, AnnAssign)

                # all functions nuke child functions except top level of course
                if (not is_toplevel) and is_fun:
                    detype_body(child_node, antr_name=antr_name, fun_name=child_node.name)
                    detype_fun_params(child_node)
                    detype_fun_ret(child_node)

                elif (not is_toplevel) and is_class:
                    detype_body(child_node, antr_name=child_node.name, fun_name=fun_name)

                elif is_assign:
                    child_node.type_comment = None

                elif is_annassign:
                    child_node.__class__ = Assign
                    child_node.targets = [child_node.target]
                    if getattr(child_node, "value", None) is None:
                        child_node.value = Constant(value=None)
                    if hasattr(child_node, "annotation"):
                        del child_node.annotation
                    child_node.type_comment = None

        def detype_walker(node: AST, antr_name: str | None = None, fun_name: str | None = None):
            for child_node in iter_child_nodes(node):
                is_fun = isinstance(child_node, FunctionDef)
                is_class = isinstance(child_node, ClassDef)
                if is_fun:
                    if fun_should_be_detyped(child_node.name, antr_name = antr_name):
                        detype_body(child_node)
                        detype_fun_params(child_node)
                        detype_fun_ret(child_node)
                elif is_class:
                    detype_walker(child_node, antr_name = child_node.name, fun_name = fun_name)

        detype_walker(tree)
        # we also need to handling type erasing the top level
        if guide[TOP_LEVEL]:
            detype_body(tree)
        return unparse(tree)

    @staticmethod
    def _perm_name(perm):
        return hex(int("".join(str(int(b)) for b in perm), 2))

    def _perm_from_name(self, perm_str: str):
        n = int(perm_str, 16)
        bits = bin(n)[2:].ljust(self.fun_count(), "0")
        return tuple(c == "1" for c in bits)

    @staticmethod
    def file_trunc(file_name: str):
        trunc_name, *xts = file_name.split(".")
        assert len(xts) < 2, "multiple extensions not supported"
        assert len(xts) > 0, "extensionless files not supported"
        assert xts[0] == "py", "only '.py' files supported"
        return trunc_name

    @staticmethod
    def q_file_trunc(perm: tuple[bool], file_name: str):
        trunc_name = CinderDetyper.file_trunc(file_name)
        perm_string = CinderDetyper._perm_name(perm)
        return f"{trunc_name}_{perm_string}"

    def _renamed_lib_in_runner(self, perm: tuple[bool]):
        tree = self._read_runner_ast()
        class RenameLibImports(NodeTransformer):
            def __init__(self, old_name, new_name):
                self.old_name = old_name
                self.new_name = new_name

            def visit_Import(self, node: Import):
                for alias in node.names:
                    if alias.name == self.old_name:
                        alias.name = self.new_name
                return node

            def visit_ImportFrom(self, node: ImportFrom):
                if node.module == self.old_name:
                    node.module = self.new_name
                return node

        old_import = CinderDetyper.file_trunc(self.lib_file_name)
        new_import = CinderDetyper.q_file_trunc(perm, self.lib_file_name)
        tree = RenameLibImports(old_import, new_import).visit(tree)
        fix_missing_locations(tree)
        return unparse(tree)

    def _detype_by_permutation(self, perm: tuple[bool]):
        tree = self._read_lib_ast()
        guide = dict(zip(self.fun_names, perm))
        return self._detype_funs(tree, guide)

    def run_perportion_compiled(self):
        raise NotImplementedError

    def run_permutation(self, perm: tuple[bool]):
        self.write_permutation(perm)
        result = self.execute_permutation(perm)
        os.remove(self.perm_lib_name(perm))
        os.remove(self.perm_runner_name(perm))
        return result

    def execute_permutation(self, perm: tuple[bool]):
        assert self.scratch_dir is not None, "scratch dir not set up"
        runner_trunc = CinderDetyper.file_trunc(self.runner_file_name)
        new_runner_trunc = CinderDetyper.q_file_trunc(perm, self.runner_file_name)
        new_runner_name = f"{self.scratch_dir}/{new_runner_trunc}.py"
        t3 = Timer("run cmd")
        cmd = " ".join((
                self.python,
                "-X jit",
                f"-X jit-list-file=jitlist_{runner_trunc}.txt",
                "-X jit-enable-jit-list-wildcards",
                "-X jit-shadow-frame",
                "-X install-strict-loader",
                new_runner_name,
                *self.params
            ))

        result = run(cmd, capture_output=True, text=True, shell=True)
        t3.end()
        return result

    def write_permutation_hex(self, perm_str: str):
        self.write_permutation(self._perm_from_name(perm_str))

    def execute_permutation_hex(self, perm_str: str):
        return self.execute_permutation_hex(self._perm_from_name(perm_str))

    def run_permutation_hex(self, perm_str: str):
        return self.run_permutation(self._perm_from_name(perm_str))

    def perm_lib_name(self, perm: tuple[bool]):
        return f"{self.scratch_dir}/{CinderDetyper.q_file_trunc(perm, self.lib_file_name)}.py"

    def perm_runner_name(self, perm: tuple[bool]):
        return f"{self.scratch_dir}/{CinderDetyper.q_file_trunc(perm, self.runner_file_name)}.py"


    def write_permutation(self, perm: tuple[bool]):
        self._ensure_scratch_dir()
        t1 = Timer("retype")
        new_lib_file_string = self._detype_by_permutation(perm)
        new_runer_file_string = self._renamed_lib_in_runner(perm)
        new_lib_name = self.perm_lib_name(perm)
        new_runner_name = self.perm_runner_name(perm)
        t1.end()

        t2 = Timer("write files")
        with open(new_lib_name, mode = "w", encoding = "utf-8") as f:
            f.write(new_lib_file_string)

        with open(new_runner_name, mode = "w", encoding = "utf-8") as f:
            f.write(new_runer_file_string)
        t2.end()






# ================== AI ZONE OF AI DEATH ==========================
# ================== AI ZONE OF AI DEATH ==========================
# ================== AI ZONE OF AI DEATH ==========================
# ================== AI ZONE OF AI DEATH ==========================
# ================== AI ZONE OF AI DEATH ==========================


    def _box_suffix(self, boxes: list[tuple[int, int]] | tuple[tuple[int, int], ...]) -> str:
        """
        Compact suffix for filenames:
        "__b<count>_<8-hex-hash>"
        """
        if not boxes:
            return ""

        # Serialize box list deterministically
        s = ";".join(f"{l},{c}" for (l, c) in boxes)
        h = zlib.crc32(s.encode("ascii")) & 0xFFFFFFFF
        return f"__b{len(boxes)}_{h:08x}"


    def perm_lib_name_box(self, perm: tuple[bool], boxes: tuple[tuple[int, int], ...]) -> str:
        base = self.perm_lib_name(perm)   # existing: "<scratch>/deltablue_static_lib_0x....py"
        root, ext = os.path.splitext(base)
        return f"{root}{self._box_suffix(boxes)}{ext}"


    def perm_runner_name_box(self, perm: tuple[bool], boxes: tuple[tuple[int, int], ...]) -> str:
        base = self.perm_runner_name(perm)
        root, ext = os.path.splitext(base)
        return f"{root}{self._box_suffix(boxes)}{ext}"


    def write_boxed_permutation(self, perm, boxes, source=None):
        self._ensure_scratch_dir()

        if source is None:
            new_lib_file_string = self._detype_by_permutation(perm)
            for (line, col) in boxes:
                new_lib_file_string = self._insert_box_at(new_lib_file_string, line, col)
        else:
            new_lib_file_string = source

        new_runner_file_string = self._renamed_lib_in_runner_box(perm, boxes)

        new_lib_name = self.perm_lib_name_box(perm, boxes)
        new_runner_name = self.perm_runner_name_box(perm, boxes)

        with open(new_lib_name, "w", encoding="utf-8") as f:
            f.write(new_lib_file_string)
        with open(new_runner_name, "w", encoding="utf-8") as f:
            f.write(new_runner_file_string)






    @staticmethod
    def get_line_number_from_stderr(result: CompletedProcess[str]):
        stderr = result.stderr
        if result.returncode == 0:
            return None
        lines = stderr.splitlines()
        last = "".join(lines[-1].strip().split(":")[1:])
        try:
            return literal_eval(last)[-2:]
        except Exception:
            return None


    def _insert_box_at(self, source: str, line: int, col: int) -> str:
        tree = parse(source)

        parent: dict[AST, AST] = {}
        target: expr | None = None
        best_depth = -1

        # if col <= 0, treat as "anywhere on this line"
        if col is None or col <= 0:
            target_col = float("inf")
        else:
            target_col = col - 1  # traceback is 1-based, AST is 0-based

        def covers(node: AST) -> bool:
            if not hasattr(node, "lineno") or not hasattr(node, "col_offset"):
                return False
            if node.lineno != line:
                return False
            return node.col_offset <= target_col

        def is_box_name(node: AST) -> bool:
            return isinstance(node, Name) and node.id == "box"

        def is_box_call(node: AST) -> bool:
            return (
                isinstance(node, Call)
                and isinstance(node.func, Name)
                and node.func.id == "box"
            )

        def walk(node: AST, depth: int = 0):
            nonlocal target, best_depth
            for child in iter_child_nodes(node):
                parent[child] = node
                walk(child, depth + 1)

            # process node *after* children so depth is meaningful
            if isinstance(node, expr) and covers(node) and depth > best_depth:
                # don't target the symbol "box" itself or an existing box(...)
                if is_box_name(node) or is_box_call(node):
                    return
                target = node
                best_depth = depth

        walk(tree)

        if target is None:
            # no suitable expression found for this (line, col)
            return source

        # climb to a higher-level expression on the same line if appropriate
        cur = target
        while True:
            p = parent.get(cur)
            if not isinstance(p, expr):
                break
            if not hasattr(p, "lineno") or p.lineno != line:
                break
            # keep climbing as long as parent starts on/before the target column
            if hasattr(p, "col_offset") and p.col_offset <= target_col:
                cur = p
            else:
                break

        target = cur

        class Boxer(NodeTransformer):
            def __init__(self, target_node: expr):
                self._target = target_node

            def visit(self, node: AST):
                if node is self._target:
                    return Call(
                        func=Name(id="box", ctx=Load()),
                        args=[node],
                        keywords=[],
                    )
                return super().visit(node)

        tree = Boxer(target).visit(tree)
        fix_missing_locations(tree)
        return unparse(tree)




    def auto_box_permutation(self, perm: tuple[bool]):
        initial_result = self.run_permutation(perm)

        if initial_result.returncode == 0:
            print("permutation succeeded")
            return
        s = self._detype_by_permutation(perm)
        line, col = CinderDetyper.get_line_number_from_stderr(initial_result)
        new_source = self._insert_box_at(s, line, col)
        # print(new_source)


    def auto_box_permutation_hex(self, perm_str: str):
        self.auto_box_and_run(self._perm_from_name(perm_str))

    def auto_box_and_run(self, perm: tuple[bool]):
        """
        Try a permutation, repeatedly inserting box() at error sites.
        Up to 100 iterations, giving up if still failing.
        """
        MAX_TRIES = 100
        boxes: list[tuple[int, int]] = []

        # Start with the plain detyped code
        src = self._detype_by_permutation(perm)

        for attempt in range(MAX_TRIES):
            # Write the current version (with all accumulated boxes)
            self.write_boxed_permutation(perm, boxes, source=src)

            # Name to execute
            boxed_name = self.perm_runner_name_box(perm, tuple(boxes))


            boxed_lib_path = self.perm_lib_name_box(perm, boxes)
            new_import = CinderDetyper.file_trunc(os.path.basename(boxed_lib_path))
            print(new_import)

            cmd = " ".join((
                self.python,
                "-X jit",
                f"-X jit-list-file=jitlist_{CinderDetyper.file_trunc(self.runner_file_name)}.txt",
                "-X jit-enable-jit-list-wildcards",
                "-X jit-shadow-frame",
                "-X install-strict-loader",
                boxed_name,
                *self.params
            ))

            result = run(cmd, capture_output=True, text=True, shell=True)

            if result.returncode == 0:
                print(f"permutation succeeded after {attempt} boxes")
                return result

            # Find next error location
            loc = CinderDetyper.get_line_number_from_stderr(result)
            if not loc:
                print("error without a usable (line, col); stopping")
                print(result.stderr)
                return result

            line, col = loc
            boxes.append((line, col))

            # Insert box into source
            src = self._insert_box_at(src, line, col)

        print(f"failed after {MAX_TRIES} box attempts")
        print(result.stderr)
        return result

    def _renamed_lib_in_runner_box(self, perm: tuple[bool], boxes):
        # start from the original runner AST
        tree = self._read_runner_ast()

        base_name = CinderDetyper.file_trunc(self.lib_file_name)  # "deltablue_static_lib"
        perm_lib_path = self.perm_lib_name(perm)
        perm_name = CinderDetyper.file_trunc(os.path.basename(perm_lib_path))  # "deltablue_static_lib_0x..."

        # module name for the *boxed* lib file
        boxed_lib_path = self.perm_lib_name_box(perm, boxes)
        new_import = CinderDetyper.file_trunc(os.path.basename(boxed_lib_path))

        class RenameLibImports(NodeTransformer):
            def __init__(self, base_name, new_name):
                self.base_name = base_name
                self.new_name = new_name

            def visit_Import(self, node: Import):
                for alias in node.names:
                    if self.base_name in alias.name:
                        alias.name = self.new_name
                return node

            def visit_ImportFrom(self, node: ImportFrom):
                if self.base_name in node.module:
                    node.module = self.new_name
                return node

        new_tree = RenameLibImports(base_name, new_import).visit(tree)
        fix_missing_locations(new_tree)
        return unparse(new_tree)




# ================== AI ZONE OF AI DEATH ==========================
# ================== AI ZONE OF AI DEATH ==========================
# ================== AI ZONE OF AI DEATH ==========================
# ================== AI ZONE OF AI DEATH ==========================
# ================== AI ZONE OF AI DEATH ==========================






















    def _get_prep_perm(self, preportion: float):
        typed_count = self.fun_count() * preportion
        typed_count = round(typed_count)
        untyped_count = self.fun_count() - typed_count
        return tuple(sample((False, True), counts = (typed_count, untyped_count), k=self.fun_count()))

    @staticmethod
    def _collect_failure_stats(results: dict[str, CompletedProcess[str]]):
        counts: dict[str, int] = {}
        unknown = []
        success_count = 0
        successes = []
        failures = []

        for perm, result in results.items():
            stderr = result.stderr
            if result.returncode == 0:
                success_count += 1
                successes.append(perm)
                continue

            lines = stderr.splitlines()

            last = "".join(lines[-1].strip().split(":")[1:])
            try:
                err_name = literal_eval(last)[0]
            except Exception:
                err_name = "<unknown>"
                unknown.append(stderr)

            counts[err_name] = counts.get(err_name, 0) + 1
            failures.append(str((perm,err_name)))

        return unknown, counts, success_count, successes, failures

    @staticmethod
    def _make_info_dump(results: dict[str, CompletedProcess[str]]):
        return dict((a,b.stderr) for a,b in results.items())

    def _ensure_scratch_dir(self):
        # AI wrote this but im less worried about this than the box thing
        if hasattr(self, "_ram_dir"):
            return

        base_ram = "/dev/shm" if os.path.isdir("/dev/shm") else None
        if base_ram is None:
            # last resort: /tmp, may be disk-backed
            print("ram disk not available")
            base_ram = "/tmp"

        ram_dir = tempfile.mkdtemp(prefix="cinder_xp_", dir=base_ram)
        self._ram_dir = ram_dir

        link_path = self.scratch_dir

        if link_path is None:
            self.scratch_dir = ram_dir
            def _cleanup():
                shutil.rmtree(ram_dir, ignore_errors=True)

            atexit.register(_cleanup)
            return

        # scratch_dir was provided: make it a symlink to RAM
        os.makedirs(os.path.dirname(os.path.abspath(link_path)), exist_ok=True)
        # if something already exists there, blow it away
        if os.path.islink(link_path) or os.path.isfile(link_path):
            os.unlink(link_path)
        elif os.path.isdir(link_path):
            shutil.rmtree(link_path)

        os.symlink(ram_dir, link_path)
        self.scratch_dir = link_path

        def _cleanup():
            try:
                if os.path.islink(link_path):
                    os.unlink(link_path)
            except FileNotFoundError:
                pass
            shutil.rmtree(ram_dir, ignore_errors=True)

        atexit.register(_cleanup)



    def run_experiment(self, samples = 100, granularity = 1):
        self._ensure_scratch_dir()
        def xp_gen():
            yield self._get_prep_perm(1.0)
            yield self._get_prep_perm(0.0)
            for i in range(1, self.fun_count(), granularity):
                preportion = i / self.fun_count()
                for _ in range(samples):
                    yield self._get_prep_perm(preportion)

        xps = tuple(xp_gen())
        task_args = tuple(reversed(tuple(map(tuple, zip((self,)*len(xps), xps)))))
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        trunk = CinderDetyper.file_trunc(self.lib_file_name)
        results_file_name = f"results_{trunk}_{stamp}_samples_{samples}_granularity_{granularity}.json"

        total = len(task_args)
        counter = Value('i', 0)
        lock = Lock()
        print(f"deploying {total} tasks")
        results = dict()

        with Pool(cpu_count(), initializer=_init_worker, initargs=(counter, lock)) as pool:
            async_res = pool.map_async(run_perm_worker, task_args)
            bar_width = 100
            while not async_res.ready():
                done = counter.value
                frac = done / total
                filled = int(frac * bar_width)
                print(f"\r[{'#' * filled}{'-' * (bar_width - filled)}] {done}/{total} {round(10000 * (done/total)) / 100}%", end="", flush=True)
                sleep(0.1)
            print(f"\r[{'#'*bar_width}] {total}/{total} 100%", end="", flush=True)
            print()
            results = dict(async_res.get())

        unknowns, failure_stats, success_count, successes, failures = CinderDetyper._collect_failure_stats(results)

        total = len(results)
        failure_count = total - success_count
        print(f"{success_count} successes, {failure_count} failures out of {total}")

        with open(results_file_name, "w", encoding="utf-8") as f:
            dump(
                {
                    "source": self.lib_file_name,
                    "success count": success_count,
                    "failure count": failure_count,
                    "failure stats": failure_stats,
                    "successes": successes,
                    "failures": failures,
                    "unknowns": unknowns,
                    "info_dump": CinderDetyper._make_info_dump(results),
                },
                f,
                indent=2,
            )
        print(f"results in {results_file_name}")

def main():
    delta_blue = CinderDetyper("deltablue_static.py", "/vol/python", "scratch3" , params = ("10",))
    delta_blue.run_experiment()
    # 0x80020804100
    # delta_blue.auto_box_permutation_hex("0x2b5440213810e")

    fannkuch = CinderDetyper("fannkuch_static.py", "/vol/python", "experiment_3")
    fannkuch.run_experiment()

    nbody = CinderDetyper("nbody_static.py", "/vol/python", "experiment_3")
    nbody.run_experiment()

    nqueens = CinderDetyper("nqueens_static.py", "/vol/python", "experiment_3")
    nqueens.run_experiment()

    richards = CinderDetyper("richards_static.py", "/vol/python", "experiment_3")
    richards.run_experiment()


if __name__ == "__main__":
    main()
