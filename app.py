"""Axiom Math educational API. Conservative prototype; do not expose publicly without hardening."""
from __future__ import annotations
import importlib.util, sys, uuid
from pathlib import Path
from typing import Any
import sympy as sp
from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel, Field

ROOT = Path(__file__).resolve().parents[1]
CORE_PATH = ROOT / "axiom_math_core_all_in_one.py"
spec = importlib.util.spec_from_file_location("axiom_core", CORE_PATH)
core = importlib.util.module_from_spec(spec); sys.modules[spec.name] = core
assert spec.loader is not None; spec.loader.exec_module(core)
app = FastAPI(title="Axiom Math", version="0.2.0", description="Educational mathematics solver prototype")
app.add_middleware(CORSMiddleware, allow_origins=["*"], allow_methods=["*"], allow_headers=["*"])

class SolveRequest(BaseModel):
    equation: str = Field(min_length=1, max_length=1025)
    variable: str = Field(default="x", min_length=1, max_length=32)
    detail: str = Field(default="steps", pattern="^(answer|steps|detailed)$")
class CheckRequest(BaseModel):
    equation: str = Field(min_length=1, max_length=1025)
    variable: str = Field(default="x", min_length=1, max_length=32)
    answer: str = Field(min_length=1, max_length=512)
class SystemRequest(BaseModel):
    equations: list[str] = Field(min_length=2, max_length=12)
    variables: list[str] = Field(min_length=2, max_length=8)
    detail: str = Field(default="steps", pattern="^(answer|steps|detailed)$")
class InequalityRequest(BaseModel):
    inequality: str = Field(min_length=3, max_length=1025)
    variable: str = Field(default="x", min_length=1, max_length=32)
    detail: str = Field(default="steps", pattern="^(answer|steps|detailed)$")
class FunctionRequest(BaseModel):
    expression: str = Field(min_length=1, max_length=1025)
    variable: str = Field(default="x", min_length=1, max_length=32)
    operation: str = Field(pattern="^(simplify|factor|expand|differentiate|integrate|limit|domain|plot_points)$")
    point: str | None = Field(default=None, max_length=128)
    detail: str = Field(default="steps", pattern="^(answer|steps|detailed)$")
class ValidateRequest(BaseModel):
    protocol_version: str = "1.0"
    task_id: str | None = None
    variables: list[str]
    equations: list[str]
    options: dict[str, dict[str, str]]
    limits: dict[str, Any] = {"timeout_ms": 5000}


def _valid_vars(names: list[str]):
    if not names or len(names) > 8 or len(set(names)) != len(names): raise ValueError("Укажи от 1 до 8 разных переменных")
    if any(not n.isidentifier() or n in {"pi", "e", "sin", "cos", "tan", "sqrt", "log", "abs"} or len(n)>32 for n in names): raise ValueError("Используй простые имена переменных, например x, y")
    return [sp.Symbol(n, real=True) for n in names]

def _expr(source: str, names: list[str]):
    # Accept common school notation while preserving strict AST parsing.
    source = source.strip().replace("^", "**").replace("π", "pi")
    parser = core.SafeExpressionParser(names)
    result = parser.parse(source)
    return result, parser.constraints

def _equation(source: str, names: list[str]):
    if source.count("=") != 1: raise ValueError("Уравнение должно содержать ровно один знак =")
    left, right = source.split("=", 1)
    lhs, lc = _expr(left, names); rhs, rc = _expr(right, names)
    return lhs-rhs, lc+rc

def _fmt(x): return str(x).replace("**", "^")
def _linear_steps(expr, x, equation, roots):
    if expr.is_polynomial(x) and sp.degree(expr, x) == 1:
        a=sp.simplify(sp.diff(expr,x)); b=sp.simplify(expr.subs(x,0))
        return [f"Перенесём всё в левую часть: {_fmt(expr)} = 0.", f"Получаем линейное уравнение: {_fmt(a)}·{x} + ({_fmt(b)}) = 0.", f"Переносим свободный член и делим на коэффициент при {x}.", f"{x} = {_fmt(roots[0])}."] if roots else [f"Приводим уравнение к виду {_fmt(expr)} = 0.", "Получаем противоречие: решений нет."]
    if expr.is_polynomial(x) and sp.degree(expr,x)==2:
        poly=sp.Poly(expr,x); a,b,c=poly.all_coeffs(); d=sp.simplify(b*b-4*a*c)
        return [f"Приводим к квадратному уравнению: {_fmt(expr)} = 0.", f"Коэффициенты: a={_fmt(a)}, b={_fmt(b)}, c={_fmt(c)}.", f"Дискриминант: D = b² − 4ac = {_fmt(d)}.", "Находим корни по формуле x = (−b ± √D)/(2a).", "Корни: "+(", ".join(_fmt(r) for r in roots) if roots else "действительных корней нет")+"."]
    return [f"Исходное уравнение: {equation}.", f"Переносим правую часть в левую: {_fmt(expr)} = 0.", "Используем символьное решение в действительных числах.", "Полученный результат: "+(", ".join(_fmt(r) for r in roots) if roots else "решений в действительных числах нет")+"."]

@app.get("/api/health")
def health(): return {"ok":True,"app":"Axiom Math","version":"0.2.0","features":["equations","systems","inequalities","functions","calculus","photo-ocr-ui","history"]}

@app.post("/api/solve")
def solve(req:SolveRequest):
    try:
        x=_valid_vars([req.variable.strip()])[0]; var=str(x)
        expr,constraints=_equation(req.equation,[var])
        solset=sp.solveset(expr,x,domain=sp.S.Reals)
        roots=list(solset) if isinstance(solset,sp.FiniteSet) else []
        filtered=[]
        for root in roots:
            allowed=core.evaluate_constraints(constraints,{x:root})
            if allowed is not False: filtered.append(root)
        if solset is sp.S.EmptySet or solset==sp.S.EmptySet: answer="Решений в действительных числах нет."
        elif isinstance(solset,sp.FiniteSet): answer=(", ".join(f"{var} = {_fmt(r)}" for r in filtered) if filtered else "Решений с учётом области определения нет.")
        else: answer=f"Множество решений: {_fmt(solset)}"
        steps=_linear_steps(expr,x,req.equation,filtered)
        if req.detail=="answer": steps=[]
        elif req.detail=="detailed": steps += [f"Проверка: подстановка найденных значений в исходное уравнение и проверка ограничений области определения.", "Ограничения: "+("; ".join(map(str,constraints)) if constraints else "явных ограничений парсера не обнаружено")+"."]
        return {"ok":True,"mode":"solve","equation":req.equation,"answer":answer,"solutions":[_fmt(r) for r in filtered],"solution_set":_fmt(solset),"steps":steps,"detail":req.detail,"note":"Символьный результат нужно проверять для задач с параметрами и особыми областями определения."}
    except (SyntaxError,TypeError,ValueError) as e: raise HTTPException(400,f"Не удалось разобрать запись: {str(e)[:220]}")
    except Exception as e: raise HTTPException(422,f"Решение не удалось получить уверенно ({type(e).__name__}). Упрости запись или проверь область определения.")

@app.post("/api/check")
def check(req:CheckRequest):
    try:
        _valid_vars([req.variable.strip()])
        payload={"protocol_version":"1.0","task_id":str(uuid.uuid4()),"variables":[req.variable.strip()],"equations":[req.equation.replace("^","**")],"options":{"Введённый ответ":{req.variable.strip():req.answer.replace("^","**")}},"limits":{"timeout_ms":8000}}
        return {"ok":True,"result":core.validate_request(payload)}
    except Exception as e: raise HTTPException(400,f"Не удалось проверить ответ: {str(e)[:220]}")

@app.post("/api/system")
def solve_system(req:SystemRequest):
    try:
        symbols=_valid_vars([v.strip() for v in req.variables]); names=[str(s) for s in symbols]
        if len(req.equations)>12: raise ValueError("Слишком много уравнений")
        eqs=[_equation(eq,names)[0] for eq in req.equations]
        result=sp.solve(eqs,symbols,dict=True)
        answer="; ".join(" , ".join(f"{s} = {_fmt(d.get(s,sp.Symbol(str(s))))}" for s in symbols) for d in result) if result else "Конечного набора решений не найдено (возможно, система несовместна или имеет бесконечно много решений)."
        steps=["Записываем каждое уравнение в виде левой части минус правой части = 0.","Решаем уравнения совместно относительно: "+", ".join(names)+".","Результат: "+answer]
        if req.detail=="answer": steps=[]
        elif req.detail=="detailed": steps += ["Проверяйте найденные значения подстановкой во все исходные уравнения.","Для нелинейных систем возможны дополнительные ограничения и решения, требующие отдельной проверки."]
        return {"ok":True,"mode":"system","answer":answer,"solutions":[{str(k):_fmt(v) for k,v in d.items()} for d in result],"steps":steps}
    except (SyntaxError,TypeError,ValueError) as e: raise HTTPException(400,f"Ошибка в системе: {str(e)[:220]}")
    except Exception as e: raise HTTPException(422,f"Не удалось решить систему уверенно ({type(e).__name__}).")

@app.post("/api/inequality")
def inequality(req:InequalityRequest):
    try:
        x=_valid_vars([req.variable.strip()])[0]; src=req.inequality.strip().replace("≤","<=").replace("≥",">=")
        import re
        match=re.fullmatch(r"(.+?)(<=|>=|<|>)(.+)",src)
        if not match: raise ValueError("Используй одно неравенство, например x^2 - 4 >= 0")
        left,op,right=match.groups(); lhs,_=_expr(left,[str(x)]); rhs,_=_expr(right,[str(x)]); expr=lhs-rhs
        relation={"<":sp.Lt,"<=":sp.Le,">":sp.Gt,">=":sp.Ge}[op](expr,0)
        sol=sp.solve_univariate_inequality(relation,x,relational=False,domain=sp.S.Reals)
        steps=[f"Переносим всё в одну сторону: {_fmt(expr)} {op} 0.","Определяем нули выражения и критические точки.",f"Записываем промежутки, где знак соответствует неравенству: {_fmt(sol)}."]
        if req.detail=="answer": steps=[]
        elif req.detail=="detailed": steps += ["На границах проверяем, включаются ли точки: при ≤ и ≥ нули обычно включаются, если выражение определено.","Проверь знаки на каждом промежутке и исключи точки, где исходное выражение не определено."]
        return {"ok":True,"mode":"inequality","answer":_fmt(sol),"steps":steps}
    except (SyntaxError,TypeError,ValueError) as e: raise HTTPException(400,f"Не удалось разобрать неравенство: {str(e)[:220]}")
    except Exception as e: raise HTTPException(422,f"Не удалось решить неравенство уверенно ({type(e).__name__}).")

@app.post("/api/function")
def function(req:FunctionRequest):
    try:
        x=_valid_vars([req.variable.strip()])[0]; expr,_=_expr(req.expression,[str(x)])
        steps=[f"Исходное выражение: f({x}) = {_fmt(expr)}."]
        if req.operation=="simplify": out=sp.simplify(expr); label="Упрощение"; steps += ["Применяем алгебраические тождества и упрощение."]
        elif req.operation=="factor": out=sp.factor(expr); label="Разложение на множители"; steps += ["Ищем множители выражения."]
        elif req.operation=="expand": out=sp.expand(expr); label="Раскрытие скобок"; steps += ["Раскрываем произведения и степени."]
        elif req.operation=="differentiate": out=sp.diff(expr,x); label="Производная"; steps += [f"Дифференцируем по {x}, применяя правила производной."]
        elif req.operation=="integrate": out=sp.integrate(expr,x); label="Первообразная"; steps += [f"Интегрируем по {x}; константа интегрирования обозначается C."]; out=sp.Integral(expr,x) if out.has(sp.Integral) else out
        elif req.operation=="limit":
            if req.point is None: raise ValueError("Для предела укажи точку, например 0 или oo")
            p=sp.oo if req.point.strip().lower() in {"oo","inf","infinity","бесконечность"} else _expr(req.point,[str(x)])[0]
            out=sp.limit(expr,x,p); label=f"Предел при {x} → {_fmt(p)}"; steps += ["Подставляем точку напрямую, если это возможно, иначе вычисляем предел."]
        elif req.operation=="domain":
            out=sp.calculus.util.continuous_domain(expr,x,sp.S.Reals); label="Область определения"; steps += ["Ищем действительные значения переменной, при которых выражение определено."]
        else:
            out=[(i,sp.simplify(expr.subs(x,i))) for i in range(-5,6)]; label="Точки графика"; steps += ["Вычисляем значения функции для целых x от −5 до 5."]
        answer=("; ".join(f"x={a}: y={_fmt(b)}" for a,b in out) if isinstance(out,list) else _fmt(out))
        if req.detail=="answer": steps=[]
        elif req.detail=="detailed": steps += [f"Результат операции «{label}»: {answer}.","Автоматические шаги объясняют общий метод; для сложных выражений они не заменяют полное доказательство каждого преобразования."]
        return {"ok":True,"mode":"function","label":label,"answer":answer,"steps":steps}
    except (SyntaxError,TypeError,ValueError) as e: raise HTTPException(400,f"Ошибка выражения: {str(e)[:220]}")
    except Exception as e: raise HTTPException(422,f"Операцию не удалось выполнить уверенно ({type(e).__name__}).")

@app.post("/api/validate")
def validate(req:ValidateRequest): return core.validate_request(req.model_dump())

FORMULAS={
"Алгебра": ["(a+b)² = a²+2ab+b²","(a−b)² = a²−2ab+b²","a²−b² = (a−b)(a+b)","a³+b³ = (a+b)(a²−ab+b²)","a³−b³ = (a−b)(a²+ab+b²)","ax+b=0 ⇒ x=−b/a, a≠0","D=b²−4ac; x=(−b±√D)/(2a)"],
"Геометрия": ["Прямоугольник: S=ab, P=2(a+b)","Треугольник: S=ah/2","Теорема Пифагора: a²+b²=c²","Круг: S=πr², C=2πr","Трапеция: S=(a+b)h/2","Призма: V=Sосн·h","Цилиндр: V=πr²h","Шар: V=4πr³/3, S=4πr²"],
"Тригонометрия": ["sin²x+cos²x=1","tg x=sin x/cos x","sin(a±b)=sin a cos b ± cos a sin b","cos(a±b)=cos a cos b ∓ sin a sin b","1+tg²x=1/cos²x"],
"Производные и интегралы": ["(xⁿ)'=n·xⁿ⁻¹","(sin x)'=cos x","(cos x)'=−sin x","(eˣ)'=eˣ","∫xⁿdx=xⁿ⁺¹/(n+1)+C, n≠−1","∫1/x dx=ln|x|+C","∫cos x dx=sin x+C"],
"Логарифмы и степени": ["a^m·a^n=a^(m+n)","a^m/a^n=a^(m−n), a≠0","(a^m)^n=a^(mn)","log_a(xy)=log_a x+log_a y","log_a(x/y)=log_a x−log_a y","log_a(x^r)=r·log_a x","log_a b=ln b/ln a"],
"Последовательности": ["Арифметическая: a_n=a_1+(n−1)d","Сумма арифметической: S_n=n(a_1+a_n)/2","Геометрическая: b_n=b_1·q^(n−1)","Сумма геометрической: S_n=b_1(q^n−1)/(q−1), q≠1"],
"Аналитическая геометрия и векторы": ["Расстояние: d=√((x₂−x₁)²+(y₂−y₁)²)","Середина отрезка: ((x₁+x₂)/2,(y₁+y₂)/2)","Уравнение прямой: y=kx+b","Скалярное произведение: a·b=|a||b|cosθ","Длина вектора (x,y): √(x²+y²)"],
"Комплексные числа": ["i²=−1","(a+bi)+(c+di)=(a+c)+(b+d)i","|a+bi|=√(a²+b²)","(a+bi)(a−bi)=a²+b²"],
"Комбинаторика": ["n!=1·2·…·n","Размещения: A_n^k=n!/(n−k)!","Сочетания: C_n^k=n!/(k!(n−k)!)","Перестановки: P_n=n!"],
"Вероятность и статистика": ["P(A)=m/n для равновозможных исходов","E(X)=Σxᵢpᵢ","Среднее арифметическое: x̄=Σxᵢ/n","Дисперсия: D(X)=E(X²)−(E(X))²","P(A∪B)=P(A)+P(B)−P(A∩B)","Для независимых событий: P(A∩B)=P(A)P(B)"],
"Физика — базовые формулы": ["Скорость: v=s/t","Плотность: ρ=m/V","Сила: F=ma","Работа: A=Fs (если сила вдоль движения)","Мощность: P=A/t","Закон Ома: I=U/R"]}
@app.get("/api/formulas")
def formulas(): return {"ok":True,"categories":FORMULAS}

WEB_DIR=ROOT/"web"
@app.get("/",include_in_schema=False)
def home(): return FileResponse(WEB_DIR/"index.html")
app.mount("/static",StaticFiles(directory=WEB_DIR),name="static")
@app.get("/manifest.webmanifest",include_in_schema=False)
def manifest(): return FileResponse(WEB_DIR/"manifest.webmanifest",media_type="application/manifest+json")
@app.get("/sw.js",include_in_schema=False)
def service_worker(): return FileResponse(WEB_DIR/"sw.js",media_type="application/javascript")
