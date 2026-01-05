from ast import parse, unparse, FunctionDef, ClassDef, AnnAssign, Assign, expr, Name, iter_child_nodes, AST, fix_missing_locations, JoinedStr, NodeTransformer, Import, ImportFrom, literal_eval, Constant, Call, Attribute, Load, iter_fields
from functools import cache, reduce
from itertools import chain
from random import sample
from subprocess import run, CompletedProcess
from time import perf_counter
from multiprocessing import Pool, cpu_count
from datetime import datetime
from json import dump, dumps
from builtins import __dict__ as btn_dict
from multiprocessing import Value, Lock
from time import sleep
from tempfile import mkdtemp
from atexit import register
from os import remove, path, makedirs, unlink, symlink
from shutil import rmtree
from typing import Tuple
import black

def split_lines(src: str) -> str:
    return black.format_str(src, mode=black.Mode(line_length=1))

Permutation = Tuple[bool, ...]
BoxSet = Tuple[Tuple[int, int], ...]
ErrorTuple = Tuple[str, str, int, int]
ShortErrorTuple = Tuple[str, int, int]

def is_builtin_class_name(name: str):
    return name in btn_dict and isinstance(btn_dict[name], type)

TIME = False
TOP_LEVEL = (None, None)
GuideKey = tuple[str | None, str | None]
GuideType = dict[GuideKey, bool]
QNameType = set[GuideKey]

class Timer:
    def __init__(self, name):
        self.name = name
        self.start = perf_counter() if TIME else 0

    def end(self):
        if TIME:
            dt = perf_counter() - self.start
            print(f"{self.name}: {dt:.6f}s")


#holds globals for permutation workers
class PermutationLocker:
    _g_counter = None
    _g_lock = None

    @staticmethod
    def _init_worker(counter, lock):
        PermutationLocker._g_counter = counter
        PermutationLocker._g_lock = lock

    @staticmethod
    def run_perm_worker(args):
        me, perm = args
        stderr = me.run_permutation(perm)
        with PermutationLocker._g_lock:
            PermutationLocker._g_counter.value += 1
        return CinderDetyper._perm_name(perm), stderr

    @staticmethod
    def run_boxer_worker(args):
        me, perm = args
        try:
            result = me.box_set_of_permutation(perm)
        except Exception as e:
            result = str(e)
        with PermutationLocker._g_lock:
            PermutationLocker._g_counter.value += 1
        return CinderDetyper._perm_name(perm), result

class CinderDetyper:
    permutation_to_result = dict()
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
        ordered_q_names = [TOP_LEVEL]
        q_fun_names_set: QNameType = {TOP_LEVEL}

        antr_graph: dict[None | str, frozenset[str]] = {None: frozenset()}

        # NO ONE should be using any of these except _enumerate_funs
        def antr_classes(anter_exprs: list[expr]) -> frozenset[str]:
            assert all(isinstance(a, Name) for a in anter_exprs), "only simple inheritance supported"

            # direct bases
            antr_names: tuple[str, ...] = tuple(a.id for a in anter_exprs if a.id in antr_graph)
            anter_set: frozenset[str] = frozenset(antr_names)
            antr_name_sets: tuple[frozenset[str], ...] = tuple(frozenset(antr_graph[antr_name]) for antr_name in antr_names)
            return reduce(lambda a, b: a.union(b), antr_name_sets, anter_set)

        def update_antr_graph(class_node: ClassDef):
            class_name = class_node.name
            assert class_name not in antr_graph, "class name shadowing not supported"
            antr_graph[class_name] = frozenset(antr_classes(class_node.bases))

        def antr_fun_gen(fun_name: str, antr_name: str | None = None):
            assert antr_name in antr_graph, f"function somehow processed before class ancestors: {antr_name} {fun_name}\n{antr_graph}"
            anters = antr_graph[antr_name]
            return tuple((anter, fun_name) for anter in anters)

        def fun_exists(antr_name: str | None, fun_name: str):
            # Check against the set for speed
            return (antr_name, fun_name) in q_fun_names_set

        def is_fun_overload(fun_name: str, antr_name: str | None = None):
            assert not fun_exists(antr_name, fun_name), "function name shadowing not supported"
            return not any(fun_exists(*q_name) for q_name in antr_fun_gen(fun_name, antr_name = antr_name))

        def count_gen(node: AST, antr_name: str | None = None, fun_name: str | None = None):
            inside_fun = fun_name is not None
            inside_class = antr_name is not None
            for child_node in iter_child_nodes(node):
                is_fun = isinstance(child_node, FunctionDef)
                is_class = isinstance(child_node, ClassDef)
                assert not (is_fun and inside_fun), "function inside function not supported"
                assert not (is_class and inside_fun), "class inside function not supported"
                assert not (is_class and inside_class), "class inside class not supported"
                if is_fun:
                    if is_fun_overload(child_node.name, antr_name):
                        key = (antr_name, child_node.name)
                        q_fun_names_set.add(key)
                        ordered_q_names.append(key)
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

        # Verify counts match
        assert fun_count == len(ordered_q_names), "function counting logic failure: function name count != new function count"

        # Return the ORDERED list converted to a tuple
        return antr_graph, tuple(ordered_q_names)

    def _detype_funs(self, tree: AST, guide: GuideType) -> str:

        # NO ONE should be using any of these except _detype_funs
        @cache
        def get_fun_q_names(fun_name: str, antr_name = None):
            assert antr_name in self.class_antrs, "class ancestor graph incomplete"
            anters = self.class_antrs[antr_name]
            anter_fun_names = tuple(q_name for q_name in zip(anters, (fun_name,) * len(anters)) if q_name in self.fun_names)
            return ((antr_name, fun_name),) + anter_fun_names

        def get_fun_q_name(fun_name: str, antr_name = None) -> GuideKey:
            q_fun_name, *alternate_names = get_fun_q_names(fun_name, antr_name = antr_name)
            assert len(alternate_names) <= 1, f"function identity failure: one of {alternate_names}"
            return alternate_names[0] if alternate_names else q_fun_name

        def fun_should_be_detyped(fun_name: str, antr_name: str | None = None):
            q_fun_name: GuideKey = get_fun_q_name(fun_name, antr_name = antr_name)
            assert q_fun_name in guide, "function type status unspecified"
            return guide[q_fun_name]

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
        #return string so cache behaves well
        return split_lines(unparse(tree))

    @cache
    @staticmethod
    def _perm_name(perm: Permutation) -> str:
        return hex(int("".join(str(int(b)) for b in perm), 2))

    @cache
    def _perm_from_name(self, perm_str: str) -> Permutation:
        n = int(perm_str, 16)
        bits = bin(n)[2:].ljust(self.fun_count(), "0")
        return tuple(c == "1" for c in bits)

    @cache
    @staticmethod
    def file_trunc(file_name: str):
        trunc_name, *xts = file_name.split(".")
        assert len(xts) < 2, "multiple extensions not supported"
        assert len(xts) > 0, "extensionless files not supported"
        assert xts[0] == "py", "only '.py' files supported"
        return trunc_name

    @cache
    @staticmethod
    def q_file_trunc(perm: Permutation, file_name: str):
        trunc_name = CinderDetyper.file_trunc(file_name)
        perm_string = CinderDetyper._perm_name(perm)
        return f"{trunc_name}_{perm_string}"

    @cache
    def _renamed_lib_in_runner(self, perm: Permutation):
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
        # return string so cache behaves well
        return split_lines(unparse(tree))

    def _detype_by_permutation(self, perm: Permutation) -> str:
        tree = self._read_lib_ast()
        guide: GuideType = dict(zip(self.fun_names, perm))
        return self._detype_funs(tree, guide)

    def run_perportion_compiled(self):
        raise NotImplementedError

    def run_permutation(self, perm: Permutation) -> CompletedProcess[str]:
        self.write_permutation(perm)
        result = self.execute_permutation(perm)
        # remove(self.perm_lib_name(perm))
        # remove(self.perm_runner_name(perm))
        return result

    def execute_permutation(self, perm: Permutation):
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
        return self.execute_permutation_hex(perm_str)

    def run_permutation_hex(self, perm_str: str):
        return self.run_permutation(self._perm_from_name(perm_str))

    def perm_lib_name(self, perm: Permutation):
        return f"{self.scratch_dir}/{CinderDetyper.q_file_trunc(perm, self.lib_file_name)}.py"

    def perm_runner_name(self, perm: Permutation):
        return f"{self.scratch_dir}/{CinderDetyper.q_file_trunc(perm, self.runner_file_name)}.py"


    def write_permutation(self, perm: Permutation):
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

    def _get_prep_perm(self, preportion: float):
        typed_count = self.fun_count() * preportion
        typed_count = round(typed_count)
        untyped_count = self.fun_count() - typed_count
        return tuple(sample((False, True), counts = (typed_count, untyped_count), k=self.fun_count()))

    @staticmethod
    def _collect_failure_stats(results: dict[str, CompletedProcess[str]]):
        counts = {}
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

            error_tuple = CinderDetyper._error_tuple(result)
            err_name, err_file, err_line, err_col = error_tuple
            if err_line == -1:
                unknown.append(stderr)
            else:
                assert err_col == 0, f"col not zero {perm} {error_tuple}"

            counts[err_name] = counts.get(err_name, 0) + 1
            failures.append(str((perm, err_name)))

        return unknown, counts, success_count, successes, failures

    @staticmethod
    def _make_info_dump(results: dict[str, CompletedProcess[str]]):
        return dict((a,b.stderr) for a,b in results.items())

    def _ensure_scratch_dir(self):
        return
        if hasattr(self, "_ram_dir"):
            return

        base_ram = "/dev/shm" if path.isdir("/dev/shm") else None
        if base_ram is None:
            # last resort: /tmp, may be disk-backed
            print("ram disk not available")
            base_ram = "/tmp"

        ram_dir = mkdtemp(prefix="cinder_xp_", dir=base_ram)
        self._ram_dir = ram_dir

        link_path = self.scratch_dir

        if link_path is None:
            self.scratch_dir = ram_dir
            def _cleanup():
                rmtree(ram_dir, ignore_errors=True)

            register(_cleanup)
            return

        # scratch_dir was provided: make it a symlink to RAM
        makedirs(path.dirname(path.abspath(link_path)), exist_ok=True)
        # if something already exists there, blow it away
        if path.islink(link_path) or path.isfile(link_path):
            unlink(link_path)
        elif path.isdir(link_path):
            rmtree(link_path)

        symlink(ram_dir, link_path)
        self.scratch_dir = link_path

        def _cleanup():
            try:
                if path.islink(link_path):
                    unlink(link_path)
            except FileNotFoundError:
                pass
            rmtree(ram_dir, ignore_errors=True)
        register(_cleanup)

    def find_permutation_errors(self, samples = 2, granularity = 1):
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

        with Pool(cpu_count(), initializer=PermutationLocker._init_worker, initargs=(counter, lock)) as pool:
            async_res = pool.map_async(PermutationLocker.run_perm_worker, task_args)
            bar_width = 10
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

    def find_permutation_is_boxable(self, samples = 50, granularity = 1):
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
        results_file_name = f"results_BOXES_{trunk}_{stamp}_samples_{samples}_granularity_{granularity}.json"

        total = len(task_args)
        counter = Value('i', 0)
        lock = Lock()
        print(f"deploying {total} tasks")
        results = dict()

        with Pool(cpu_count(), initializer=PermutationLocker._init_worker, initargs=(counter, lock)) as pool:
            async_res = pool.map_async(PermutationLocker.run_boxer_worker, task_args)
            bar_width = 10
            while not async_res.ready():
                done = counter.value
                frac = done / total
                filled = int(frac * bar_width)
                print(f"\r[{'#' * filled}{'-' * (bar_width - filled)}] {done}/{total} {round(10000 * (done/total)) / 100}%", end="", flush=True)
                sleep(0.1)
            print(f"\r[{'#'*bar_width}] {total}/{total} 100%", end="", flush=True)
            print()
            results = dict(async_res.get())

        with open(results_file_name, "w", encoding="utf-8") as f:
            dump(results, f, indent=2, sort_keys=True)
        print(f"results in {results_file_name}")



# auto-box

    @cache
    def box_set_name(self, box_set: BoxSet) -> str:
        return "".join(tuple("".join(tuple(map(hex, box))) for box in box_set))

    @cache
    def box_set_of_permutation_hex(self, perm_id: str) -> BoxSet:
        return self.box_set_of_permutation(self._perm_from_name(perm_id))

    @staticmethod
    def _error_tuple(result: CompletedProcess[str]) -> ErrorTuple:
        stderr = result.stderr
        lines = stderr.splitlines()
        last = "".join(lines[-1].strip().split(":")[1:])
        try:
            out = literal_eval(last)
        except Exception:
            out = ("<unknown>", "<file name>", -1, -1)

        assert len(out) == 4, f"poorly formatted error: {out}"
        return out

    @staticmethod
    def _short_error_tuple(result: CompletedProcess[str]) -> ErrorTuple:
        return CinderDetyper._shorten_error_tuple(CinderDetyper._error_tuple(result))

    @staticmethod
    def _shorten_error_tuple(t: ErrorTuple) -> ShortErrorTuple:
        a, b, c, d = t
        if "/" in b:
            file_name = b.split("/")[-1].split(".")[0]
            return (a.replace(file_name, "<file>"), c, d)
        return (a, c, d)

    @cache
    @staticmethod
    def _err_tup_eq(t1: ErrorTuple, t2: ErrorTuple) -> bool:
        return CinderDetyper._shorten_error_tuple(t1) == CinderDetyper._shorten_error_tuple(t2)

    def box_set_of_permutation(self, perm: Permutation) -> BoxSet | None:
        init_result = self.run_permutation(perm)
        if init_result.returncode == 0:
            return ()
        init_err_tup = CinderDetyper._short_error_tuple(init_result)
        errors: set[ShortErrorTuple] = frozenset([init_err_tup])
        err_name, err_line, _ = init_err_tup
        # print(self.perm_lib_name(perm), init_err_tup)
        # TODO: extract type name from error name to do casts
        box_count = self._count_expers_on_line_perm(perm, err_line)
        if box_count == 0:
            return None
        for i in range(box_count):
            result = self.box_set_of_permutation_helper(perm, ((err_line, i),), errors)
            if result is not None:
                return result
        return None

    def _count_expers_on_line_perm_with_boxes(self, perm: Permutation, box_set_t: BoxSet, line: int) -> int:
        src = self._detype_by_permutation_with_boxes(perm, box_set_t)
        tree = parse(src, type_comments=True)
        return len(self._expers_on_line(tree, line))

    @cache
    def box_set_of_permutation_helper(self, perm: Permutation, box_set_t: BoxSet, p_errors: frozenset[ShortErrorTuple]) -> BoxSet | None:
        init_result = self.run_perm_with_boxes(perm, box_set_t)
        if init_result.returncode == 0:
            return () # fixes all errors
        init_err_tup = CinderDetyper._short_error_tuple(init_result)
        if init_err_tup in p_errors or init_err_tup[1] == -1:
            return None # does not fix any errors
        errors = p_errors.union([init_err_tup])
        # print(self.perm_lib_name_with_boxes(perm, box_set_t), init_err_tup)
        err_name, err_line, _ = init_err_tup
        box_count = self._count_expers_on_line_perm_with_boxes(perm, box_set_t, err_line)
        if box_count == 0:
            return None
        for i in range(box_count):
            result = self.box_set_of_permutation_helper(perm, box_set_t + ((err_line, i),), errors)
            if result is not None:
                return result
        return None

    def _count_expers_on_line_perm(self, perm: Permutation, line: int) -> int:
        return len(self._expers_on_line(parse(self._detype_by_permutation(perm)), line))

    def _expers_on_line(self, ast: AST, line_number: int) -> Tuple[Tuple[expr, expr], ...]:
        expressions_on_line = []
        def visit_node(parent, node):
            if isinstance(node, expr) and hasattr(node, 'lineno') and node.lineno == line_number:
                expressions_on_line.append((parent, node))
            for child in iter_child_nodes(node):
                visit_node(node, child)
        visit_node(None, ast)
        expressions_on_line.sort(key=lambda x: getattr(x, 'col_offset', 0))
        return expressions_on_line

    def run_perm_with_boxes(self, perm: Permutation, box_set_t: BoxSet) -> CompletedProcess[str]:
        self.write_permutation_with_boxes(perm, box_set_t)
        result = self.execute_permutation_with_boxes(perm, box_set_t)
        return result


    def perm_lib_name_with_boxes(self, perm: Permutation, box_set_t: BoxSet):
        base_name = CinderDetyper.q_file_trunc(perm, self.lib_file_name)
        box_set_name = self.box_set_name(box_set_t)
        base_name = f"{base_name}_{box_set_name}"
        return f"{self.scratch_dir}/{base_name}.py"

    def perm_runner_name_with_boxes(self, perm: Permutation, box_set_t: BoxSet):
        base_name = CinderDetyper.q_file_trunc(perm, self.runner_file_name)
        box_set_name = self.box_set_name(box_set_t)
        base_name = f"{base_name}_{box_set_name}"
        return f"{self.scratch_dir}/{base_name}.py"

    def write_permutation(self, perm: Permutation):
        self._ensure_scratch_dir()
        t1 = Timer("retype")
        new_lib_file_string = self._detype_by_permutation(perm)
        new_runer_file_string = self._renamed_lib_in_runner(perm)
        new_lib_name = self.perm_lib_name(perm)  # Now uses default box_set_t=()
        new_runner_name = self.perm_runner_name(perm)  # Now uses default box_set_t=()
        t1.end()

        t2 = Timer("write files")
        with open(new_lib_name, mode = "w", encoding = "utf-8") as f:
            f.write(new_lib_file_string)

        with open(new_runner_name, mode = "w", encoding = "utf-8") as f:
            f.write(new_runer_file_string)
        t2.end()

    def execute_permutation_with_boxes(self, perm: Permutation, box_set_t: BoxSet):
        assert self.scratch_dir is not None, "scratch dir not set up"
        runner_trunc = CinderDetyper.file_trunc(self.runner_file_name)
        new_runner_name = self.perm_runner_name_with_boxes(perm, box_set_t)
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
        return result

    def write_permutation_with_boxes(self, perm: Permutation, box_set_t: BoxSet):
        self._ensure_scratch_dir()
        new_lib_file_string = self._detype_by_permutation_with_boxes(perm, box_set_t)
        new_runner_file_string = self._renamed_lib_in_runner_with_boxes(perm, box_set_t)
        new_lib_name = self.perm_lib_name_with_boxes(perm, box_set_t)
        new_runner_name = self.perm_runner_name_with_boxes(perm, box_set_t)
        with open(new_lib_name, mode="w", encoding="utf-8") as f:
            f.write(new_lib_file_string)
        with open(new_runner_name, mode="w", encoding="utf-8") as f:
            f.write(new_runner_file_string)

    @cache
    def _renamed_lib_in_runner_with_boxes(self, perm: Permutation, box_set_t: BoxSet) -> str:
        tree = self._read_runner_ast()
        class RenameLibImports(NodeTransformer):
            def __init__(self, old_name, new_name):
                self.old_name = old_name
                self.new_name = new_name

            def visit_Import(self, node: Import):
                for alias in node.names:
                    if alias.name.startswith(self.old_name):
                        alias.name = self.new_name
                return node

            def visit_ImportFrom(self, node: ImportFrom):
                if node.module.startswith(self.old_name):
                    node.module = self.new_name
                return node

        old_import = CinderDetyper.file_trunc(self.lib_file_name)
        new_import = f"{CinderDetyper.q_file_trunc(perm, self.lib_file_name)}_{self.box_set_name(box_set_t)}"
        tree = RenameLibImports(old_import, new_import).visit(tree)
        fix_missing_locations(tree)
        # return string so cache behaves well
        return split_lines(unparse(tree))

    @staticmethod
    @cache
    def file_trunc_with_boxes(file_name: str, box_set_t: BoxSet) -> str:
        return CinderDetyper.file_trunc(file_name)

    def do_not_box(self, parent, exper):
        is_joined_string = isinstance(parent, JoinedStr)
        is_box_call = isinstance(exper, Call) and isinstance(exper.func, Name) and exper.func.id == "box"
        is_box = isinstance(exper, Name) and exper.id == "box"
        is_self = isinstance(exper, Name) and exper.id == "self"
        is_in_box_call = isinstance(parent, Call) and isinstance(parent.func, Name) and parent.func.id == "box"
        return is_joined_string or is_box_call or is_box or is_self or is_in_box_call

    @cache
    def _detype_by_permutation_with_boxes(self, perm: Permutation, box_set_t: BoxSet) -> str:
        if len(box_set_t) == 0:
            return self._detype_by_permutation(perm)
        box_set = list(box_set_t)
        line, index = box_set.pop()
        one_less = self._detype_by_permutation_with_boxes(perm, tuple(box_set))
        tree = parse(one_less)  # Fresh parse each time
        parent, exper = self._expers_on_line(tree, line)[index]
        if self.do_not_box(parent, exper):
            return one_less
        boxed = Call(
            func=Name(id="box", ctx=Load()),
            args=[exper],
            keywords=[],
        )
        for field, value in iter_fields(parent):
            if value is exper:
                setattr(parent, field, boxed)
                break
            elif isinstance(value, list) and exper in value:
                value[value.index(exper)] = boxed
                break
        fix_missing_locations(tree)
        return split_lines(unparse(tree))


def main():
    delta_blue = CinderDetyper("deltablue_static.py", "/vol/python", "experiment_3" , params = ("10",))
    delta_blue.find_permutation_is_boxable()
    # 0x3bf7f607bdf77 0x3edfafffdf7f9
    # print(delta_blue.box_set_of_permutation_hex("0x3bf7f607bdf77"))
    # CinderDetyper._short_error_tuple(("can't box non-primitive deltablue_static_lib_0x3bf7f607bdf77_0x870x10x870x40x870x10x870x10x870x10x870x1.UrnaryConstraint", 135, 0))


    # fannkuch = CinderDetyper("fannkuch_static.py", "/vol/python", "experiment_3")
    # fannkuch.find_permutation_errors()

    # nbody = CinderDetyper("nbody_static.py", "/vol/python", "experiment_3")
    # nbody.find_permutation_errors()
    # nbody.find_permutation_is_boxable()
    # 0x21d

    # nqueens = CinderDetyper("nqueens_static.py", "/vol/python", "experiment_3")
    # nqueens.find_permutation_errors()

    # richards = CinderDetyper("richards_static.py", "/vol/python", "experiment_3")
    # richards.find_permutation_errors()


if __name__ == "__main__":
    main()
