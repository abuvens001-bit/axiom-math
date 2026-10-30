"""Axiom Math Core v0.6.0 — all-in-one edition.

Includes the validator and deterministic regression tests in one file.
Requirements: Python 3.10+ and SymPy (pip install sympy).

Normal JSON CLI:
    python axiom_math_core_all_in_one.py < request.json

Run embedded tests:
    python axiom_math_core_all_in_one.py --self-test

This remains a conservative prototype, not a hardened sandbox.
"""
"""Axiom Math Core v0.6.0 — educational real-domain answer validator.

This is a conservative prototype for validating candidate answers to school-level
real-valued equations. It does NOT execute input as Python and does NOT use
SymPy's parse_expr. It is not a complete computer algebra system or a hardened
sandbox for hostile multi-tenant services. Run untrusted workloads in a separately
restricted OS/container with memory and CPU limits.

Python: 3.10+
Dependency: SymPy
CLI protocol: one JSON request on stdin, one JSON response on stdout.
"""

import ast
import json
import math
import multiprocessing as mp
import re
import sys
import time
from fractions import Fraction
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import sympy as sp

__version__ = "0.6.0"
PROTOCOL_VERSION = "1.0"


class ValidationStatus:
    VERIFIED = "VERIFIED"
    REJECTED = "REJECTED"
    UNDETERMINED = "UNDETERMINED"
    INVALID_INPUT = "INVALID_INPUT"


class ViolationReason:
    NONE = "NONE"
    DOMAIN_VIOLATION = "DOMAIN_VIOLATION"
    IDENTITY_VIOLATION = "IDENTITY_VIOLATION"
    SYNTAX_ERROR = "SYNTAX_ERROR"
    SECURITY_VIOLATION = "SECURITY_VIOLATION"
    TIMEOUT_EXCEEDED = "TIMEOUT_EXCEEDED"
    WORKER_FAILURE = "WORKER_FAILURE"


# Conservative limits. Adjust only alongside tests and a threat model.
MAX_EXPR_LENGTH = 512
MAX_AST_NODES = 160
MAX_AST_DEPTH = 32
MAX_ABS_CONSTANT = 1_000_000
MAX_ABS_EXPONENT_NUMERATOR = 1_000
MAX_EXPONENT_DENOMINATOR = 100
MAX_EQUATIONS = 20
MAX_OPTIONS = 20
MAX_VARIABLES = 20
MAX_VARIABLE_NAME_LENGTH = 32
MAX_LABEL_LENGTH = 40
MAX_TOTAL_TEXT_CHARS = 30_000
MAX_TIMEOUT_SECONDS = 60.0
MAX_DETAILS_LENGTH = 240

# Constraint tuple: (kind, expression). Expressions are constructed only by the
# AST whitelist compiler, never from eval/parse_expr.
Constraint = Tuple[str, sp.Expr]
_VAR_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]{0,31}\Z")


def _error_result(reason: str, details: str = "") -> dict:
    out = {
        "global_error": True,
        "status": ValidationStatus.INVALID_INPUT,
        "reason": reason,
    }
    if details:
        out["details"] = str(details)[:MAX_DETAILS_LENGTH]
    return out


def _constant_fraction(node: ast.AST) -> Fraction:
    """Read a small rational literal/expression without evaluating Python code."""
    if isinstance(node, ast.Constant):
        value = node.value
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            raise ValueError("Показатель степени должен быть числовой константой")
        if isinstance(value, float) and not math.isfinite(value):
            raise ValueError("NaN и бесконечности запрещены")
        if abs(value) > MAX_ABS_CONSTANT:
            raise ValueError("Числовая константа превышает лимит")
        # str(float) preserves the familiar decimal representation (e.g. 0.1),
        # avoiding binary-float approximation in school arithmetic.
        return Fraction(str(value)) if isinstance(value, float) else Fraction(value, 1)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
        value = _constant_fraction(node.operand)
        return -value if isinstance(node.op, ast.USub) else value
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Div)):
        left = _constant_fraction(node.left)
        right = _constant_fraction(node.right)
        if isinstance(node.op, ast.Add):
            result = left + right
        elif isinstance(node.op, ast.Sub):
            result = left - right
        elif isinstance(node.op, ast.Mult):
            result = left * right
        else:
            if right == 0:
                raise ValueError("Деление на ноль в показателе степени")
            result = left / right
        if abs(result.numerator) > MAX_ABS_EXPONENT_NUMERATOR or result.denominator > MAX_EXPONENT_DENOMINATOR:
            raise ValueError("Показатель степени превышает безопасные ограничения")
        return result
    raise ValueError("Разрешены только простые рациональные показатели степени")


class SafeExpressionParser:
    """Compile a strict mathematical subset of Python syntax into SymPy."""

    FUNCTIONS = {"sin", "cos", "tan", "ctg", "cot", "sqrt", "log", "abs"}

    def __init__(self, allowed_vars: Iterable[str]):
        self.allowed_vars = set(allowed_vars)
        self.constraints: List[Constraint] = []
        self.node_count = 0

    def parse(self, source: str) -> sp.Expr:
        if type(source) is not str:
            raise TypeError("Выражение должно быть строкой")
        if len(source) > MAX_EXPR_LENGTH:
            raise ValueError("Превышена максимальная длина выражения")
        source = source.strip()
        if not source:
            raise SyntaxError("Пустое выражение")
        # Trim only outer whitespace: '1 2' must remain invalid, not become '12'.
        try:
            tree = ast.parse(source, mode="eval")
        except (SyntaxError, ValueError, MemoryError, RecursionError) as exc:
            raise SyntaxError("Некорректный синтаксис выражения") from exc
        return self._compile(tree.body, depth=1)

    def _count(self, node: ast.AST, depth: int) -> None:
        self.node_count += 1
        if self.node_count > MAX_AST_NODES:
            raise ValueError("Превышен лимит числа узлов AST")
        if depth > MAX_AST_DEPTH:
            raise ValueError("Превышена максимальная глубина AST")

    @staticmethod
    def _check_constant(value: Any) -> None:
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            raise ValueError("Разрешены только числовые константы")
        if isinstance(value, float) and not math.isfinite(value):
            raise ValueError("NaN и бесконечности запрещены")
        if abs(value) > MAX_ABS_CONSTANT:
            raise ValueError("Числовая константа превышает лимит")

    def _count_subtree(self, node: ast.AST, depth: int) -> None:
        self._count(node, depth)
        for child in ast.iter_child_nodes(node):
            self._count_subtree(child, depth + 1)

    def _compile(self, node: ast.AST, depth: int) -> sp.Expr:
        self._count(node, depth)
        child_depth = depth + 1

        if isinstance(node, ast.Constant):
            self._check_constant(node.value)
            if isinstance(node.value, int):
                result = sp.Integer(node.value)
            else:
                result = sp.Rational(str(node.value))
            return result

        if isinstance(node, ast.Name):
            if node.id == "pi":
                return sp.pi
            if node.id not in self.allowed_vars:
                raise ValueError(f"Неизвестная или запрещённая переменная: {node.id}")
            return sp.Symbol(node.id, real=True)

        if isinstance(node, ast.UnaryOp):
            if not isinstance(node.op, (ast.USub, ast.UAdd)):
                raise ValueError("Эта унарная операция запрещена")
            operand = self._compile(node.operand, child_depth)
            result = -operand if isinstance(node.op, ast.USub) else operand
            return result

        if isinstance(node, ast.BinOp):
            left = self._compile(node.left, child_depth)
            if isinstance(node.op, ast.Pow):
                # The exponent subtree is counted even though it is compiled as a
                # constant rational, not as a general symbolic expression.
                self._count_subtree(node.right, child_depth)
                exponent = _constant_fraction(node.right)
                if abs(exponent.numerator) > MAX_ABS_EXPONENT_NUMERATOR or exponent.denominator > MAX_EXPONENT_DENOMINATOR:
                    raise ValueError("Показатель степени превышает безопасные ограничения")
                if exponent <= 0:
                    # Treat 0**0 as outside the supported real-domain convention.
                    self.constraints.append(("nonzero", left))
                if exponent.denominator % 2 == 0:
                    self.constraints.append(("nonnegative", left))
                    result = left ** sp.Rational(exponent.numerator, exponent.denominator)
                elif exponent.denominator == 1:
                    result = left ** exponent.numerator
                else:
                    # Real odd roots, unlike the principal complex power, preserve
                    # school-level real arithmetic for negative bases.
                    result = sp.real_root(left, exponent.denominator) ** exponent.numerator
                return result

            right = self._compile(node.right, child_depth)
            if isinstance(node.op, ast.Add):
                result = left + right
            elif isinstance(node.op, ast.Sub):
                result = left - right
            elif isinstance(node.op, ast.Mult):
                result = left * right
            elif isinstance(node.op, ast.Div):
                self.constraints.append(("nonzero", right))
                result = left / right
            else:
                raise ValueError(f"Операция {type(node.op).__name__} запрещена")
            return result

        if isinstance(node, ast.Call):
            if not isinstance(node.func, ast.Name):
                raise ValueError("Вызовы методов объектов запрещены")
            name = node.func.id
            if name not in self.FUNCTIONS:
                raise ValueError(f"Функция {name} запрещена")
            if node.keywords:
                raise ValueError("Именованные аргументы запрещены")
            if name == "log" and len(node.args) not in (1, 2):
                raise ValueError("log ожидает один аргумент и необязательное основание")
            if name != "log" and len(node.args) != 1:
                raise ValueError(f"{name} ожидает ровно один аргумент")
            args = [self._compile(arg, child_depth) for arg in node.args]
            if name == "sin":
                result = sp.sin(args[0])
            elif name == "cos":
                result = sp.cos(args[0])
            elif name == "tan":
                self.constraints.append(("nonzero", sp.cos(args[0])))
                result = sp.tan(args[0])
            elif name in ("ctg", "cot"):
                self.constraints.append(("nonzero", sp.sin(args[0])))
                result = sp.cot(args[0])
            elif name == "sqrt":
                self.constraints.append(("nonnegative", args[0]))
                result = sp.sqrt(args[0])
            elif name == "log":
                self.constraints.append(("positive", args[0]))
                if len(args) == 1:
                    result = sp.log(args[0])
                else:
                    self.constraints.append(("positive", args[1]))
                    self.constraints.append(("not_one", args[1]))
                    result = sp.log(args[0]) / sp.log(args[1])
            else:  # abs
                result = sp.Abs(args[0])
            return result

        raise ValueError(f"Конструкция AST {type(node).__name__} запрещена")

def _prove_zero(expr: sp.Expr) -> Optional[bool]:
    """True/False only when SymPy establishes zero/nonzero; otherwise unknown."""
    try:
        value = sp.simplify(expr)
        if value == 0 or value.is_zero is True:
            return True
        if value.is_zero is False:
            return False
        value = sp.trigsimp(sp.expand(value))
        if value == 0 or value.is_zero is True:
            return True
        if value.is_zero is False:
            return False
        numerator, _denominator = sp.fraction(sp.together(value))
        if numerator == 0 or numerator.is_zero is True:
            return True
    except (ArithmeticError, TypeError, ValueError, NotImplementedError, RecursionError, MemoryError):
        return None
    return None


def _prove_sign(expr: sp.Expr) -> Tuple[Optional[bool], Optional[bool]]:
    """Return (is_positive, is_negative), using only definite symbolic facts."""
    try:
        value = sp.simplify(expr)
        if value.is_positive is True:
            return True, False
        if value.is_negative is True:
            return False, True
        if value.is_zero is True:
            return False, False
        if value.is_real is False:
            return None, None
    except (ArithmeticError, TypeError, ValueError, NotImplementedError, RecursionError, MemoryError):
        pass
    return None, None


def evaluate_constraints(constraints: Sequence[Constraint], substitutions: Dict[sp.Symbol, sp.Expr]) -> Optional[bool]:
    """True=valid, False=violation, None=not provable. Unknown never passes."""
    unknown = False
    for kind, original_expr in constraints:
        try:
            value = sp.simplify(original_expr.subs(substitutions))
        except Exception:
            return None
        if kind == "nonzero":
            zero = _prove_zero(value)
            if zero is True:
                return False
            if zero is None:
                unknown = True
        elif kind == "nonnegative":
            zero = _prove_zero(value)
            if zero is True:
                continue
            positive, negative = _prove_sign(value)
            if negative is True:
                return False
            if positive is not True:
                unknown = True
        elif kind == "positive":
            zero = _prove_zero(value)
            if zero is True:
                return False
            positive, negative = _prove_sign(value)
            if negative is True:
                return False
            if positive is not True:
                unknown = True
        elif kind == "not_one":
            zero = _prove_zero(value - 1)
            if zero is True:
                return False
            if zero is None:
                unknown = True
        else:
            return None
    return None if unknown else True


def _parse_candidate(value: Any) -> sp.Expr:
    if type(value) is not str:
        raise TypeError("Значение переменной должно быть строкой")
    parser = SafeExpressionParser(set())
    expr = parser.parse(value)
    if expr.free_symbols:
        raise ValueError("В значении ответа не допускаются переменные")
    domain = evaluate_constraints(parser.constraints, {})
    if domain is False:
        raise ValueError("Значение ответа нарушает ОДЗ")
    if domain is None:
        raise ValueError("Не удалось доказать допустимость значения ответа")
    return expr


def _clean_details(exc: BaseException) -> str:
    return str(exc).replace("\n", " ")[:MAX_DETAILS_LENGTH]


def _worker(equations: Sequence[str], options: Dict[str, Dict[str, str]], var_names: Sequence[str], conn) -> None:
    """Child process entry point. IPC payloads are bounded plain dictionaries."""
    try:
        vars_map = {name: sp.Symbol(name, real=True) for name in var_names}
        parsed_equations: List[sp.Expr] = []
        all_constraints: List[Constraint] = []

        for equation in equations:
            left_source, right_source = equation.split("=", 1)
            left_parser = SafeExpressionParser(var_names)
            right_parser = SafeExpressionParser(var_names)
            left_expr = left_parser.parse(left_source)
            right_expr = right_parser.parse(right_source)
            parsed_equations.append(left_expr - right_expr)
            all_constraints.extend(left_parser.constraints)
            all_constraints.extend(right_parser.constraints)

        results: Dict[str, Dict[str, Any]] = {}
        for label, coordinates in options.items():
            try:
                substitutions: Dict[sp.Symbol, sp.Expr] = {}
                for name in var_names:
                    substitutions[vars_map[name]] = _parse_candidate(coordinates[name])

                domain = evaluate_constraints(all_constraints, substitutions)
                if domain is False:
                    results[label] = {"status": ValidationStatus.REJECTED, "reason": ViolationReason.DOMAIN_VIOLATION, "verified": False}
                    continue

                unknown = domain is None
                failed_equation = False
                for expression in parsed_equations:
                    verdict = _prove_zero(expression.subs(substitutions))
                    if verdict is False:
                        failed_equation = True
                        break
                    if verdict is None:
                        unknown = True

                if failed_equation:
                    results[label] = {"status": ValidationStatus.REJECTED, "reason": ViolationReason.IDENTITY_VIOLATION, "verified": False}
                elif unknown:
                    results[label] = {"status": ValidationStatus.UNDETERMINED, "reason": ViolationReason.NONE, "verified": False}
                else:
                    results[label] = {"status": ValidationStatus.VERIFIED, "reason": ViolationReason.NONE, "verified": True}
            except (SyntaxError, TypeError, ValueError, KeyError) as exc:
                message = str(exc)
                reason = ViolationReason.DOMAIN_VIOLATION if "нарушает ОДЗ" in message else ViolationReason.SYNTAX_ERROR
                results[label] = {"status": ValidationStatus.INVALID_INPUT, "reason": reason, "verified": False, "details": _clean_details(exc)}
            except Exception as exc:
                results[label] = {"status": ValidationStatus.UNDETERMINED, "reason": ViolationReason.NONE, "verified": False, "details": f"Не удалось доказать результат: {type(exc).__name__}"}

        conn.send({"global_error": False, "options": results})
    except BaseException as exc:
        try:
            conn.send(_error_result(ViolationReason.WORKER_FAILURE, type(exc).__name__))
        except Exception:
            pass
    finally:
        conn.close()


def _bounded_cleanup(process, diagnostic: bool = False) -> bool:
    """Terminate child with bounded waits; never call an unbounded join."""
    try:
        if process.is_alive():
            if diagnostic:
                print("[CLEANUP] terminate", flush=True)
            process.terminate()
            process.join(0.5)
        if process.is_alive() and hasattr(process, "kill"):
            if diagnostic:
                print("[CLEANUP] kill escalation", flush=True)
            process.kill()
            process.join(0.5)
        alive = process.is_alive()
        if diagnostic:
            print(f"[CLEANUP] alive={alive}; exitcode={process.exitcode}", flush=True)
        return alive
    except (AssertionError, OSError, ValueError):
        return True


def _normalize_request(equations_list: Any, options_dict: Any, var_names: Any) -> Tuple[list, dict, list]:
    """Validate and copy inputs into plain built-in types before multiprocessing."""
    if type(equations_list) not in (list, tuple) or not 1 <= len(equations_list) <= MAX_EQUATIONS:
        raise ValueError(f"Количество уравнений должно быть от 1 до {MAX_EQUATIONS}")
    equations: List[str] = []
    for equation in equations_list:
        if type(equation) is not str or len(equation) > 2 * MAX_EXPR_LENGTH + 1 or equation.count("=") != 1:
            raise ValueError("Каждое уравнение должно быть строкой вида левая_часть=правая_часть")
        left, right = equation.split("=", 1)
        if not left.strip() or not right.strip() or len(left) > MAX_EXPR_LENGTH or len(right) > MAX_EXPR_LENGTH:
            raise ValueError("Пустая или слишком длинная часть уравнения")
        equations.append(equation)

    if type(var_names) in (set, frozenset):
        names = sorted(var_names) if all(type(x) is str for x in var_names) else []
    elif type(var_names) in (list, tuple):
        names = list(var_names)
    else:
        raise ValueError("variables должен быть списком или множеством имён")
    if not 1 <= len(names) <= MAX_VARIABLES:
        raise ValueError(f"Количество переменных должно быть от 1 до {MAX_VARIABLES}")
    if any(type(name) is not str or len(name) > MAX_VARIABLE_NAME_LENGTH or not _VAR_RE.fullmatch(name) or name == "pi" for name in names):
        raise ValueError("Недопустимое имя переменной")
    if len(set(names)) != len(names):
        raise ValueError("Имена переменных должны быть уникальными")

    if type(options_dict) is not dict or not 1 <= len(options_dict) <= MAX_OPTIONS:
        raise ValueError(f"Количество вариантов должно быть от 1 до {MAX_OPTIONS}")
    options: Dict[str, Dict[str, str]] = {}
    for label, coordinates in options_dict.items():
        if type(label) is not str or not label or len(label) > MAX_LABEL_LENGTH:
            raise ValueError("Недопустимая метка варианта")
        if type(coordinates) is not dict or set(coordinates) != set(names):
            raise ValueError(f"Вариант {label!r}: набор переменных не совпадает с variables")
        copied: Dict[str, str] = {}
        for name in names:
            value = coordinates[name]
            if type(value) is not str or len(value) > MAX_EXPR_LENGTH:
                raise ValueError(f"Вариант {label!r}: значение {name} должно быть короткой строкой")
            copied[name] = value
        options[label] = copied

    total_chars = sum(map(len, equations)) + sum(len(k) + sum(len(n) + len(v) for n, v in vals.items()) for k, vals in options.items()) + sum(map(len, names))
    if total_chars > MAX_TOTAL_TEXT_CHARS:
        raise ValueError("Общий объём входного текста превышает лимит")
    return equations, options, names


def run_secure_validation(
    equations_list: Any,
    options_dict: Any,
    var_names: Any,
    timeout_seconds: float = 5.0,
    start_method: Optional[str] = None,
    diagnostic: bool = False,
) -> dict:
    """Validate candidates in an isolated worker with a hard parent-side deadline.

    Defaults to spawn for cross-platform behavior. A successful result is not a
    proof against all SymPy bugs or OS-level resource exhaustion.
    """
    try:
        equations, options, names = _normalize_request(equations_list, options_dict, var_names)
    except (TypeError, ValueError, RecursionError, MemoryError) as exc:
        return _error_result(ViolationReason.SYNTAX_ERROR, _clean_details(exc))

    if isinstance(timeout_seconds, bool) or not isinstance(timeout_seconds, (int, float)) or not math.isfinite(timeout_seconds) or not 0.05 <= timeout_seconds <= MAX_TIMEOUT_SECONDS:
        return _error_result(ViolationReason.SYNTAX_ERROR, f"timeout_seconds должен быть от 0.05 до {MAX_TIMEOUT_SECONDS}")

    available = mp.get_all_start_methods()
    method = start_method or ("spawn" if "spawn" in available else available[0])
    if method not in available:
        return _error_result(ViolationReason.SYNTAX_ERROR, f"Недоступный метод multiprocessing: {method}")

    ctx = mp.get_context(method)
    parent_conn, child_conn = ctx.Pipe(duplex=False)
    process = ctx.Process(target=_worker, args=(equations, options, names, child_conn))
    started_process = False
    deadline = time.monotonic() + float(timeout_seconds)
    result: Optional[dict] = None
    got_response = False
    timed_out = False

    try:
        if diagnostic:
            print(f"[PROC] method={method}; timeout={timeout_seconds:.2f}s; starting", flush=True)
        process.start()
        started_process = True
        child_conn.close()
        if diagnostic:
            print(f"[PROC] pid={process.pid}; alive={process.is_alive()}", flush=True)

        while time.monotonic() < deadline:
            remaining = deadline - time.monotonic()
            if parent_conn.poll(min(0.1, max(0.0, remaining))):
                try:
                    received = parent_conn.recv()
                    if type(received) is dict and type(received.get("global_error")) is bool:
                        result = received
                        got_response = True
                    else:
                        result = _error_result(ViolationReason.WORKER_FAILURE, "Некорректный ответ воркера")
                except (EOFError, OSError, ValueError):
                    result = _error_result(ViolationReason.WORKER_FAILURE, "Канал IPC завершился без полного ответа")
                if diagnostic:
                    print(f"[IPC] received={got_response}; alive={process.is_alive()}; exitcode={process.exitcode}", flush=True)
                break
            if not process.is_alive():
                if diagnostic:
                    print(f"[PROC] exited without response; exitcode={process.exitcode}", flush=True)
                if parent_conn.poll(0.1):
                    try:
                        result = parent_conn.recv()
                        got_response = type(result) is dict
                    except (EOFError, OSError, ValueError):
                        pass
                break

        if result is None and not got_response and time.monotonic() >= deadline:
            timed_out = True
            if diagnostic:
                print(f"[TIMEOUT] alive={process.is_alive()}; exitcode={process.exitcode}", flush=True)

        if got_response and process.is_alive():
            process.join(min(0.25, max(0.0, deadline - time.monotonic())))
        elif started_process and not process.is_alive():
            process.join(0)
        if diagnostic and started_process:
            print(f"[JOIN] alive={process.is_alive()}; exitcode={process.exitcode}", flush=True)

        if timed_out:
            return {
                "global_error": True,
                "status": ValidationStatus.UNDETERMINED,
                "reason": ViolationReason.TIMEOUT_EXCEEDED,
                "details": "Превышен лимит времени проверки",
            }
        if result is not None:
            return result
        return _error_result(ViolationReason.WORKER_FAILURE, f"Воркер завершился без ответа (exitcode={process.exitcode})")
    except Exception as exc:
        return _error_result(ViolationReason.WORKER_FAILURE, _clean_details(exc))
    finally:
        try:
            child_conn.close()
        except OSError:
            pass
        try:
            parent_conn.close()
        except OSError:
            pass
        if started_process:
            alive = _bounded_cleanup(process, diagnostic=diagnostic)
            if not alive:
                try:
                    process.close()
                except (ValueError, OSError):
                    pass


def validate_request(request: Any) -> dict:
    """Public JSON-protocol adapter (protocol v1.0)."""
    if type(request) is not dict:
        return {"protocol_version": PROTOCOL_VERSION, "task_id": None, "global_status": "INVALID_REQUEST", "error": "Request must be a JSON object"}
    task_id = request.get("task_id")
    if task_id is not None and (type(task_id) is not str or len(task_id) > 80):
        task_id = None
    if request.get("protocol_version", PROTOCOL_VERSION) != PROTOCOL_VERSION:
        return {"protocol_version": PROTOCOL_VERSION, "task_id": task_id, "global_status": "INVALID_REQUEST", "error": "Unsupported protocol_version"}
    limits = request.get("limits", {})
    if type(limits) is not dict:
        return {"protocol_version": PROTOCOL_VERSION, "task_id": task_id, "global_status": "INVALID_REQUEST", "error": "limits must be a JSON object"}
    timeout_ms = limits.get("timeout_ms", 5000)
    if isinstance(timeout_ms, bool) or not isinstance(timeout_ms, int) or not 50 <= timeout_ms <= int(MAX_TIMEOUT_SECONDS * 1000):
        return {"protocol_version": PROTOCOL_VERSION, "task_id": task_id, "global_status": "INVALID_REQUEST", "error": "timeout_ms must be between 50 and 60000"}

    result = run_secure_validation(
        request.get("equations"), request.get("options"), request.get("variables"),
        timeout_seconds=timeout_ms / 1000.0,
    )
    if result.get("global_error"):
        reason = result.get("reason")
        global_status = "INVALID_REQUEST" if reason in {ViolationReason.SYNTAX_ERROR, ViolationReason.SECURITY_VIOLATION} else "ERROR"
        return {
            "protocol_version": PROTOCOL_VERSION,
            "task_id": task_id,
            "global_status": global_status,
            "error": {"reason": reason, "details": result.get("details", "")},
            "options": {},
        }
    return {
        "protocol_version": PROTOCOL_VERSION,
        "task_id": task_id,
        "global_status": "OK",
        "options": result.get("options", {}),
    }


def main() -> int:
    """Read one JSON object from stdin and emit one JSON object to stdout."""
    try:
        raw = sys.stdin.read(MAX_TOTAL_TEXT_CHARS + 10_000)
        if len(raw) > MAX_TOTAL_TEXT_CHARS + 9_999:
            response = {"protocol_version": PROTOCOL_VERSION, "task_id": None, "global_status": "INVALID_REQUEST", "error": "Request body too large"}
        else:
            request = json.loads(raw)
            response = validate_request(request)
    except (json.JSONDecodeError, UnicodeDecodeError, RecursionError, MemoryError) as exc:
        response = {"protocol_version": PROTOCOL_VERSION, "task_id": None, "global_status": "INVALID_REQUEST", "error": type(exc).__name__}
    sys.stdout.write(json.dumps(response, ensure_ascii=False, separators=(",", ":")) + "\n")
    sys.stdout.flush()
    return 0




# ================= EMBEDDED REGRESSION TESTS =================

"""Deterministic regression, boundary, and integration tests for Axiom Math Core.

Run: python -m unittest -v test_axiom_math_core.py
Optional extra fuzzing can be added with Hypothesis; the core test suite has no
optional test dependencies beyond SymPy.
"""

import json
import os
import subprocess
import sys
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
core = sys.modules[__name__]


class ParserBoundaryTests(unittest.TestCase):
    def assert_parse_fails(self, source, exc=(SyntaxError, ValueError, TypeError)):
        with self.assertRaises(exc):
            core.SafeExpressionParser({"x"}).parse(source)

    def test_empty_expression_rejected(self):
        self.assert_parse_fails("")

    def test_whitespace_expression_rejected(self):
        self.assert_parse_fails("  \n  ")

    def test_whitespace_does_not_merge_tokens(self):
        self.assert_parse_fails("1 2")

    def test_expression_length_limit(self):
        self.assert_parse_fails("1" * (core.MAX_EXPR_LENGTH + 1))

    def test_unknown_variable_rejected(self):
        self.assert_parse_fails("y+1")

    def test_unknown_function_rejected(self):
        self.assert_parse_fails("evil(1)")

    def test_attribute_access_rejected(self):
        self.assert_parse_fails("x.real")

    def test_bool_rejected(self):
        self.assert_parse_fails("True")

    def test_nonfinite_float_rejected(self):
        self.assert_parse_fails("1e999")

    def test_constant_limit(self):
        self.assert_parse_fails("1000001")

    def test_decimal_is_exact_rational(self):
        parsed = core.SafeExpressionParser(set()).parse("0.1+0.2")
        self.assertEqual(parsed, core.sp.Rational(3, 10))

    def test_nested_radicals_parse(self):
        self.assertIsNotNone(core.SafeExpressionParser({"x"}).parse("sqrt(sqrt(sqrt(x)))"))

    def test_fractional_even_power_records_nonnegative(self):
        parser = core.SafeExpressionParser({"x"})
        parser.parse("x**0.5")
        self.assertIn("nonnegative", [kind for kind, _ in parser.constraints])

    def test_fractional_negative_power_records_nonzero(self):
        parser = core.SafeExpressionParser({"x"})
        parser.parse("x**(-1/3)")
        self.assertIn("nonzero", [kind for kind, _ in parser.constraints])

    def test_composite_large_exponent_rejected(self):
        self.assert_parse_fails("x**(500+600)")

    def test_exponent_denominator_limit(self):
        self.assert_parse_fails("x**(1/101)")

    def test_power_of_symbol_rejected(self):
        self.assert_parse_fails("x**y")

    def test_division_constraint_recorded(self):
        parser = core.SafeExpressionParser({"x"})
        parser.parse("1/(x-2)")
        self.assertIn("nonzero", [kind for kind, _ in parser.constraints])

    def test_sqrt_constraint_recorded(self):
        parser = core.SafeExpressionParser({"x"})
        parser.parse("sqrt(x)")
        self.assertIn("nonnegative", [kind for kind, _ in parser.constraints])

    def test_log_constraints_recorded(self):
        parser = core.SafeExpressionParser({"x"})
        parser.parse("log(x,2)")
        kinds = [kind for kind, _ in parser.constraints]
        self.assertIn("positive", kinds)
        self.assertIn("not_one", kinds)

    def test_tan_pole_constraint_recorded(self):
        parser = core.SafeExpressionParser({"x"})
        parser.parse("tan(x)")
        self.assertIn("nonzero", [kind for kind, _ in parser.constraints])


class InputNormalizationTests(unittest.TestCase):
    def test_invalid_top_level_shape_returns_error(self):
        result = core.run_secure_validation("x=1", {"A": {"x": "1"}}, ["x"])
        self.assertTrue(result["global_error"])

    def test_custom_string_subclass_rejected_before_spawn(self):
        class WeirdString(str):
            pass
        result = core.run_secure_validation([WeirdString("x=1")], {"A": {"x": "1"}}, ["x"])
        self.assertTrue(result["global_error"])

    def test_invalid_variable_name_rejected(self):
        result = core.run_secure_validation(["x=1"], {"A": {"x": "1"}}, ["x;import os"])
        self.assertTrue(result["global_error"])

    def test_missing_candidate_variable_rejected_before_spawn(self):
        result = core.run_secure_validation(["x+y=3"], {"A": {"x": "1"}}, ["x", "y"])
        self.assertTrue(result["global_error"])

    def test_timeout_out_of_range_rejected(self):
        result = core.run_secure_validation(["x=1"], {"A": {"x": "1"}}, ["x"], timeout_seconds=1000)
        self.assertTrue(result["global_error"])


class IntegrationTests(unittest.TestCase):
    def check_case(self, equations, options, variables, expected_status, expected_reason):
        result = core.run_secure_validation(
            equations, options, variables, timeout_seconds=8.0, start_method="spawn"
        )
        self.assertFalse(result.get("global_error"), msg=str(result))
        actual = result["options"]["A"]
        self.assertEqual(actual.get("status"), expected_status, msg=str(actual))
        self.assertEqual(actual.get("reason"), expected_reason, msg=str(actual))

    def test_cancelled_denominator_hole_rejected(self):
        self.check_case(["(x**2-4)/(x-2)=0"], {"A": {"x": "2"}}, ["x"], "REJECTED", "DOMAIN_VIOLATION")

    def test_negative_solution_verified(self):
        self.check_case(["x+2=0"], {"A": {"x": "-2"}}, ["x"], "VERIFIED", "NONE")

    def test_sqrt_negative_rejected_by_domain(self):
        self.check_case(["sqrt(x)=0"], {"A": {"x": "-1"}}, ["x"], "REJECTED", "DOMAIN_VIOLATION")

    def test_sqrt_zero_allowed(self):
        self.check_case(["sqrt(x)=0"], {"A": {"x": "0"}}, ["x"], "VERIFIED", "NONE")

    def test_log_zero_argument_rejected(self):
        self.check_case(["log(x)=0"], {"A": {"x": "0"}}, ["x"], "REJECTED", "DOMAIN_VIOLATION")

    def test_log_base_one_rejected(self):
        self.check_case(["log(5,x-1)=1"], {"A": {"x": "2"}}, ["x"], "REJECTED", "DOMAIN_VIOLATION")

    def test_tan_pole_rejected(self):
        self.check_case(["tan(x)=0"], {"A": {"x": "pi/2"}}, ["x"], "REJECTED", "DOMAIN_VIOLATION")

    def test_tan_zero_verified(self):
        self.check_case(["tan(x)=0"], {"A": {"x": "0"}}, ["x"], "VERIFIED", "NONE")

    def test_cot_pole_rejected(self):
        self.check_case(["ctg(x)=0"], {"A": {"x": "pi"}}, ["x"], "REJECTED", "DOMAIN_VIOLATION")

    def test_cot_pi_over_two_verified(self):
        self.check_case(["ctg(x)=0"], {"A": {"x": "pi/2"}}, ["x"], "VERIFIED", "NONE")

    def test_square_root_fractional_power(self):
        self.check_case(["x**(1/2)=2"], {"A": {"x": "4"}}, ["x"], "VERIFIED", "NONE")

    def test_even_root_fractional_power_negative_base_rejected(self):
        self.check_case(["x**0.5=2"], {"A": {"x": "-4"}}, ["x"], "REJECTED", "DOMAIN_VIOLATION")

    def test_real_cube_root_of_negative_number(self):
        self.check_case(["x**(1/3)=-2"], {"A": {"x": "-8"}}, ["x"], "VERIFIED", "NONE")

    def test_two_thirds_power_of_negative_number(self):
        self.check_case(["x**(2/3)=4"], {"A": {"x": "-8"}}, ["x"], "VERIFIED", "NONE")

    def test_negative_fractional_power_at_zero_rejected(self):
        self.check_case(["x**(-1/3)=1"], {"A": {"x": "0"}}, ["x"], "REJECTED", "DOMAIN_VIOLATION")

    def test_decimal_exactness(self):
        self.check_case(["x=0.3"], {"A": {"x": "0.1+0.2"}}, ["x"], "VERIFIED", "NONE")

    def test_wrong_answer_rejected(self):
        self.check_case(["x=1"], {"A": {"x": "2"}}, ["x"], "REJECTED", "IDENTITY_VIOLATION")

    def test_bad_candidate_function_rejected(self):
        self.check_case(["x=1"], {"A": {"x": "evil(0)"}}, ["x"], "INVALID_INPUT", "SYNTAX_ERROR")

    def test_division_by_zero_candidate_never_verified(self):
        result = core.run_secure_validation(["x=1"], {"A": {"x": "1/0"}}, ["x"], start_method="spawn")
        self.assertFalse(result.get("global_error"), msg=str(result))
        self.assertNotEqual(result["options"]["A"]["status"], "VERIFIED")

    def test_many_identity_options(self):
        options = {f"N{i}": {"x": str(i - 10)} for i in range(20)}
        result = core.run_secure_validation(["x+x=2*x"], options, ["x"], start_method="spawn")
        self.assertFalse(result.get("global_error"), msg=str(result))
        self.assertEqual(len(result["options"]), 20)
        self.assertTrue(all(item["status"] == "VERIFIED" for item in result["options"].values()))

    def test_json_protocol_rejects_non_object_limits(self):
        result = core.validate_request({"protocol_version": "1.0", "limits": "bad"})
        self.assertEqual(result["global_status"], "INVALID_REQUEST")

    def test_json_protocol_rejects_unsupported_version(self):
        result = core.validate_request({"protocol_version": "99.0"})
        self.assertEqual(result["global_status"], "INVALID_REQUEST")

    def test_json_protocol_adapter(self):
        request = {
            "protocol_version": "1.0", "task_id": "test-001", "variables": ["x"],
            "equations": ["x+1=3"], "options": {"A": {"x": "2"}},
            "limits": {"timeout_ms": 8000},
        }
        result = core.validate_request(request)
        self.assertEqual(result["global_status"], "OK")
        self.assertEqual(result["task_id"], "test-001")
        self.assertTrue(result["options"]["A"]["verified"])

    def test_cli_json_roundtrip(self):
        request = {
            "protocol_version": "1.0", "task_id": "cli-001", "variables": ["x"],
            "equations": ["x=7"], "options": {"A": {"x": "7"}},
            "limits": {"timeout_ms": 8000},
        }
        script = str(Path(__file__).resolve())
        completed = subprocess.run(
            [sys.executable, script], input=json.dumps(request), text=True,
            capture_output=True, timeout=20,
        )
        self.assertEqual(completed.returncode, 0, msg=completed.stderr)
        result = json.loads(completed.stdout)
        self.assertEqual(result["global_status"], "OK", msg=str(result))
        self.assertTrue(result["options"]["A"]["verified"])




def _run_embedded_tests() -> int:
    import unittest
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    mp.freeze_support()
    if len(sys.argv) == 2 and sys.argv[1] == "--self-test":
        raise SystemExit(_run_embedded_tests())
    if len(sys.argv) != 1:
        sys.stderr.write("Usage: python axiom_math_core_all_in_one.py [--self-test]\n")
        raise SystemExit(2)
    raise SystemExit(main())
