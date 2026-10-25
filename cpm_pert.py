#!/usr/bin/env python3
"""CPM / PERT Studio: planificador de proyectos (biblioteca estándar de Python)."""
from __future__ import annotations

import csv
import json
import math
import statistics
import tkinter as tk
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from tkinter import filedialog, messagebox, ttk

EPS = 1e-8

@dataclass(frozen=True)
class Activity:
    name: str
    predecessors: tuple[str, ...]
    optimistic: float
    likely: float
    pessimistic: float

    def duration(self, mode: str) -> float:
        return self.likely if mode == "CPM" else (self.optimistic + 4*self.likely + self.pessimistic)/6

    def variance(self, mode: str) -> float:
        return 0.0 if mode == "CPM" else ((self.pessimistic-self.optimistic)/6)**2


def fmt(value: float) -> str:
    return f"{value:.2f}".rstrip("0").rstrip(".")


def analyze(activities: list[Activity], mode: str = "CPM") -> dict:
    if mode not in ("CPM", "PERT"):
        raise ValueError("El método debe ser CPM o PERT.")
    if not activities:
        raise ValueError("Agrega al menos una actividad.")
    by_name = {a.name: a for a in activities}
    if len(by_name) != len(activities):
        raise ValueError("Hay nombres de actividades repetidos.")
    successors = {name: [] for name in by_name}
    indegree = {name: 0 for name in by_name}
    for a in activities:
        if not a.name.strip() or any(ch in a.name for ch in ",;"):
            raise ValueError("Los nombres no pueden estar vacíos ni contener comas o punto y coma.")
        if not all(math.isfinite(x) and x >= 0 for x in (a.optimistic, a.likely, a.pessimistic)):
            raise ValueError(f"{a.name}: los tiempos deben ser números positivos o cero.")
        if not a.optimistic <= a.likely <= a.pessimistic:
            raise ValueError(f"{a.name}: se requiere optimista ≤ probable ≤ pesimista.")
        if len(set(a.predecessors)) != len(a.predecessors):
            raise ValueError(f"{a.name}: hay predecesoras repetidas.")
        for pred in a.predecessors:
            if pred not in by_name:
                raise ValueError(f"{a.name}: la predecesora '{pred}' no existe.")
            if pred == a.name:
                raise ValueError(f"{a.name}: una actividad no puede depender de sí misma.")
            successors[pred].append(a.name)
            indegree[a.name] += 1
    queue = deque(a.name for a in activities if indegree[a.name] == 0)
    order = []
    while queue:
        name = queue.popleft()
        order.append(name)
        for child in successors[name]:
            indegree[child] -= 1
            if indegree[child] == 0:
                queue.append(child)
    if len(order) != len(activities):
        raise ValueError("Las dependencias forman un ciclo; revisa las predecesoras.")
    times = {}
    for name in order:
        a = by_name[name]
        es = max((times[p]["EF"] for p in a.predecessors), default=0.0)
        d = a.duration(mode)
        times[name] = {"d": d, "v": a.variance(mode), "ES": es, "EF": es+d}
    finish = max((v["EF"] for v in times.values()), default=0)
    for name in reversed(order):
        nxt = successors[name]
        lf = min((times[n]["LS"] for n in nxt), default=finish)
        times[name]["LF"] = lf
        times[name]["LS"] = lf-times[name]["d"]
        times[name]["slack"] = times[name]["LS"]-times[name]["ES"]
        times[name]["critical"] = abs(times[name]["slack"]) < EPS
    critical = [n for n in order if times[n]["critical"]]
    # Enumerar rutas críticas completas de inicio a fin. Limitar la salida para DAG grandes.
    paths = []
    starters = [n for n in order if not by_name[n].predecessors]
    def explore(name, path):
        if len(paths) >= 100:
            return
        path = path + [name]
        next_critical = [n for n in successors[name] if times[n]["critical"] and abs(times[name]["EF"]-times[n]["ES"]) < EPS]
        if not next_critical and abs(times[name]["EF"]-finish) < EPS:
            paths.append(path)
        for nxt in next_critical:
            explore(nxt, path)
    for start in starters:
        if times[start]["critical"] and abs(times[start]["ES"]) < EPS:
            explore(start, [])
    variance_paths = [sum(times[n]["v"] for n in p) for p in paths]
    return {"order":order, "times":times, "duration":finish, "paths":paths,
            "critical":critical, "successors":successors, "by_name":by_name,
            "path_variances":variance_paths, "mode":mode}


EXAMPLE = [
    Activity("A", (), 2, 3, 4),
    Activity("B", ("A",), 3, 5, 7),
    Activity("C", ("A",), 1, 2, 3),
    Activity("D", ("B", "C"), 2, 4, 6),
    Activity("E", ("C",), 2, 3, 4),
    Activity("F", ("D", "E"), 1, 2, 3),
]

BG = "#0B1020"; PANEL = "#151E33"; INPUT = "#1C2941"
FG = "#F1F5FC"; MUTED = "#A5B5CE"; TEAL = "#32DAC4"; RED = "#FF7E80"
BLUE = "#6E9AF7"; BORDER = "#30425E"

class Studio(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("CPM / PERT Studio | Investigación de Operaciones")
        self.geometry("1270x820")
        self.minsize(990, 650)
        self.configure(bg=BG)
        self.activities = list(EXAMPLE)
        self.mode = tk.StringVar(value="CPM")
        self.goal = tk.StringVar(value="15")
        self.result = None
        self._build()
        self.refresh()
        self.calculate()

    def label(self, parent, text, size=11, color=FG, bold=False, **opts):
        return tk.Label(parent, text=text, bg=parent.cget("bg"), fg=color,
                        font=("Segoe UI", size, "bold" if bold else "normal"), **opts)

    def button(self, parent, text, cmd, emphasis=False):
        return tk.Button(parent, text=text, command=cmd, bg=TEAL if emphasis else INPUT,
                         fg=BG if emphasis else FG, activebackground=BLUE, activeforeground=BG,
                         relief="flat", bd=0, padx=13, pady=8, cursor="hand2",
                         font=("Segoe UI", 10, "bold"))

    def _build(self):
        # Lienzo exterior desplazable: evita que se oculten controles en
        # pantallas pequenas, con escalado de Windows o ventanas reducidas.
        outer = tk.Frame(self, bg=BG)
        outer.pack(fill="both", expand=True)
        self.page_canvas = tk.Canvas(outer, bg=BG, highlightthickness=0)
        vscroll = ttk.Scrollbar(outer, orient="vertical", command=self.page_canvas.yview)
        vscroll.pack(side="right", fill="y")
        self.page_canvas.pack(side="left", fill="both", expand=True)
        self.page_canvas.configure(yscrollcommand=vscroll.set)
        content = tk.Frame(self.page_canvas, bg=BG)
        window_id = self.page_canvas.create_window((0, 0), anchor="nw", window=content)
        content.bind("<Configure>", lambda e: self.page_canvas.configure(
            scrollregion=self.page_canvas.bbox("all")))
        self.page_canvas.bind("<Configure>", lambda e: self.page_canvas.itemconfigure(
            window_id, width=e.width))
        # Rueda de raton: desplaza la pagina, salvo en campos con scroll propio.
        def scroll_page(event):
            widget = self.winfo_containing(event.x_root, event.y_root)
            while widget is not None:
                if isinstance(widget, (ttk.Treeview, tk.Text)):
                    return
                widget = widget.master
            if event.delta:
                self.page_canvas.yview_scroll(-int(event.delta / 120) or (-1 if event.delta > 0 else 1), "units")
                return "break"
        self.bind_all("<MouseWheel>", scroll_page, add="+")
        head = tk.Frame(content, bg=BG, padx=23, pady=12); head.pack(fill="x")
        self.label(head, "◈  CPM / PERT STUDIO", 21, TEAL, True).pack(side="left")
        self.label(head, "INVESTIGACIÓN DE OPERACIONES  •  Planificación inteligente", 10, MUTED).pack(side="right")
        bar = tk.Frame(content, bg=PANEL, padx=16, pady=11); bar.pack(fill="x", padx=20)
        self.label(bar, "Método:", 11, FG, True).pack(side="left", padx=(0, 10))
        for val in ("CPM", "PERT"):
            tk.Radiobutton(bar, text=val, variable=self.mode, value=val, command=self.calculate,
                           bg=PANEL, fg=FG, selectcolor=INPUT, activebackground=PANEL,
                           activeforeground=TEAL, font=("Segoe UI", 11, "bold")).pack(side="left", padx=7)
        self.button(bar, "Ejemplo", self.load_example).pack(side="right", padx=3)
        self.button(bar, "Abrir JSON", self.open_json).pack(side="right", padx=3)
        self.button(bar, "Guardar JSON", self.save_json).pack(side="right", padx=3)
        self.button(bar, "Exportar CSV", self.export_csv).pack(side="right", padx=3)
        main = tk.PanedWindow(content, orient="horizontal", sashwidth=7, bg=BG, bd=0, showhandle=False, height=745)
        main.pack(fill="x", padx=20, pady=15)
        left = tk.Frame(main, bg=PANEL, padx=15, pady=12); right = tk.Frame(main, bg=BG)
        main.add(left, minsize=375, width=450); main.add(right, minsize=500)
        self.label(left, "01  ACTIVIDADES", 13, FG, True).pack(anchor="w", pady=(0, 4))
        self.label(left, "En CPM se usa el tiempo probable (m).", 9, MUTED).pack(anchor="w", pady=(0, 9))
        tablebox = tk.Frame(left, bg=PANEL); tablebox.pack(fill="both", expand=True)
        cols = ("act", "pred", "o", "m", "p")
        self.tree = ttk.Treeview(tablebox, columns=cols, show="headings", height=11, selectmode="browse")
        for col, title, width in [("act","Act.",52),("pred","Predecesoras",126),("o","a",44),("m","m",44),("p","b",44)]:
            self.tree.heading(col, text=title)
            self.tree.column(col, width=width, minwidth=35, anchor="center", stretch=(col=="pred"))
        self.tree.pack(fill="both", expand=True, side="left")
        sc = ttk.Scrollbar(tablebox, orient="vertical", command=self.tree.yview); sc.pack(side="right", fill="y")
        self.tree.configure(yscrollcommand=sc.set)
        self.tree.bind("<<TreeviewSelect>>", self.fill_selection)
        fields=tk.Frame(left,bg=PANEL);fields.pack(fill="x",pady=(12,5))
        self.entries={}
        for i,(key,txt) in enumerate((("act","Actividad"),("pred","Predecesoras"),("o","Optimista (a)"),("m","Probable (m)"),("p","Pesimista (b)"))):
            frame=tk.Frame(fields,bg=PANEL)
            frame.grid(row=i//2,column=i%2,sticky="ew",padx=4,pady=4)
            self.label(frame,txt,9,MUTED).pack(anchor="w")
            e=tk.Entry(frame,bg=INPUT,fg=FG,insertbackground=FG,relief="flat",font=("Segoe UI",11),width=15)
            e.pack(fill="x",ipady=7);self.entries[key]=e
        fields.grid_columnconfigure(0,weight=1);fields.grid_columnconfigure(1,weight=1)
        actions=tk.Frame(left,bg=PANEL);actions.pack(fill="x",pady=8)
        self.button(actions,"Agregar / actualizar",self.add_update,True).pack(side="left",padx=(0,5))
        self.button(actions,"Eliminar",self.delete).pack(side="left",padx=5)
        self.button(actions,"Limpiar",self.clear_fields).pack(side="left",padx=5)
        self.button(left,"▶  CALCULAR PROYECTO",self.calculate,True).pack(fill="x",pady=(5,6))
        self.label(left,"a ≤ m ≤ b  •  Predecesoras: A, B, C  •  Nombres únicos",9,MUTED,wraplength=360,justify="left").pack(anchor="w")
        summary=tk.Frame(right,bg=BG);summary.pack(fill="x")
        self.metrics={}
        for i,(key,title) in enumerate((("duration","DURACIÓN TOTAL"),("critical","ACTIVIDADES CRÍTICAS"),("paths","RUTAS CRÍTICAS"))):
            c=tk.Frame(summary,bg=PANEL,padx=14,pady=11)
            c.grid(row=0,column=i,sticky="nsew",padx=(0 if i==0 else 7,0))
            self.label(c,title,9,MUTED,True).pack(anchor="w")
            v=self.label(c,"—",19,TEAL,True);v.pack(anchor="w",pady=(5,0));self.metrics[key]=v
            summary.grid_columnconfigure(i,weight=1)
        self.label(right,"02  DIAGRAMA DE PRECEDENCIAS",13,FG,True).pack(anchor="w",pady=(15,7))
        plotframe=tk.Frame(right,bg=PANEL);plotframe.pack(fill="both",expand=True)
        self.canvas=tk.Canvas(plotframe,bg=PANEL,highlightthickness=0,height=215)
        self.canvas.pack(fill="both",expand=True)
        self.canvas.bind("<Configure>",lambda e:self.draw_network())
        probbar=tk.Frame(right,bg=BG);probbar.pack(fill="x",pady=(12,6))
        self.label(probbar,"03  RESULTADOS Y PROCEDIMIENTO",13,FG,True).pack(side="left")
        self.button(probbar,"Calcular probabilidad",self.calculate).pack(side="right",padx=(6,0))
        goalentry=tk.Entry(probbar,textvariable=self.goal,width=6,bg=INPUT,fg=FG,insertbackground=FG,relief="flat",font=("Segoe UI",10))
        goalentry.pack(side="right",ipady=5)
        self.label(probbar,"Meta PERT:",9,MUTED).pack(side="right",padx=(0,5))
        notebook=ttk.Notebook(right);notebook.pack(fill="both",expand=True)
        tab1=tk.Frame(notebook,bg=PANEL);tab2=tk.Frame(notebook,bg=PANEL)
        notebook.add(tab1,text="  Tabla CPM / PERT  ");notebook.add(tab2,text="  Explicación y PERT  ")
        self.results=ttk.Treeview(tab1,columns=("act","d","es","ef","ls","lf","sl","status"),show="headings",height=7)
        for key,title,w in (("act","Act.",53),("d","t",52),("es","ES",52),("ef","EF",52),("ls","LS",52),("lf","LF",52),("sl","Holg.",62),("status","Estado",82)):
            self.results.heading(key,text=title);self.results.column(key,anchor="center",width=w,minwidth=40)
        self.results.pack(fill="both",expand=True,padx=6,pady=6)
        self.results.tag_configure("critical",foreground=RED)
        self.explanation=tk.Text(tab2,bg=PANEL,fg=FG,insertbackground=FG,relief="flat",font=("Consolas",10),wrap="word",padx=14,pady=10)
        self.explanation.pack(fill="both",expand=True)
        foot=tk.Frame(content,bg=BG,padx=22,pady=3);foot.pack(fill="x")
        self.status=self.label(foot,"Listo",9,MUTED);self.status.pack(side="left")
        self.label(foot,"Sin dependencias externas • Python 3",9,MUTED).pack(side="right")
        style=ttk.Style(self);style.theme_use("clam")
        style.configure("Treeview",background=INPUT,foreground=FG,fieldbackground=INPUT,rowheight=28,borderwidth=0,font=("Segoe UI",10))
        style.configure("Treeview.Heading",background=BORDER,foreground=FG,font=("Segoe UI",9,"bold"),relief="flat")
        style.map("Treeview",background=[("selected", "#28566E")])
        style.configure("TNotebook",background=BG,borderwidth=0)
        style.configure("TNotebook.Tab",background=INPUT,foreground=FG,padding=(8,7))
        style.map("TNotebook.Tab",background=[("selected",BORDER)])

    def refresh(self):
        self.tree.delete(*self.tree.get_children())
        for a in self.activities:
            self.tree.insert("", "end", iid=a.name, values=(a.name,", ".join(a.predecessors),fmt(a.optimistic),fmt(a.likely),fmt(a.pessimistic)))

    def clear_fields(self):
        self.tree.selection_remove(self.tree.selection())
        for e in self.entries.values():e.delete(0,"end")
        self.entries["act"].focus_set()

    def fill_selection(self,_event=None):
        sel=self.tree.selection()
        if not sel:return
        a=next((x for x in self.activities if x.name==sel[0]),None)
        if not a:return
        for k,v in dict(act=a.name,pred=", ".join(a.predecessors),o=fmt(a.optimistic),m=fmt(a.likely),p=fmt(a.pessimistic)).items():
            self.entries[k].delete(0,"end");self.entries[k].insert(0,v)

    def add_update(self):
        try:
            name=self.entries["act"].get().strip().upper()
            pred=tuple(x.strip().upper() for x in self.entries["pred"].get().replace(";",",").split(",") if x.strip())
            if not name or "," in name or ";" in name:
                raise ValueError("Ingresa un nombre de actividad válido (sin comas).")
            a=Activity(name,pred,*[float(self.entries[k].get().strip().replace(",",".")) for k in ("o","m","p")])
            selected=self.tree.selection()
            old=selected[0] if selected else None
            new=[x for x in self.activities if x.name not in (name,old)] + [a]
            # En una renombrada, las dependencias antiguas deben corregirse manualmente.
            analyze(new,self.mode.get())
            self.activities=new;self.refresh();self.clear_fields();self.calculate()
            self.status.config(text=f"Actividad {name} guardada correctamente")
        except (ValueError,OverflowError) as exc:messagebox.showerror("Revisa los datos",str(exc))

    def delete(self):
        selected=self.tree.selection()
        if not selected:
            messagebox.showinfo("Selecciona una actividad","Selecciona una fila para eliminar.");return
        name=selected[0]
        dependents=[a.name for a in self.activities if name in a.predecessors]
        if dependents:
            messagebox.showerror("Dependencias existentes",f"No puedes borrar {name}: depende(n) de ella {', '.join(dependents)}.")
            return
        self.activities=[a for a in self.activities if a.name!=name]
        self.refresh();self.clear_fields()
        if self.activities:self.calculate()
        else:self.result=None;self.draw_network();self.results.delete(*self.results.get_children())

    def load_example(self):
        self.activities=list(EXAMPLE);self.refresh();self.clear_fields();self.calculate()

    def calculate(self):
        try:
            r=analyze(self.activities,self.mode.get())
            self.result=r
            self.metrics["duration"].config(text=fmt(r["duration"])+" unidades")
            self.metrics["critical"].config(text=str(len(r["critical"])))
            self.metrics["paths"].config(text=str(len(r["paths"]))+("+" if len(r["paths"])>=100 else ""))
            self.results.delete(*self.results.get_children())
            for n in r["order"]:
                t=r["times"][n]
                self.results.insert("","end",values=(n,*(fmt(t[k]) for k in ("d","ES","EF","LS","LF","slack")),"CRÍTICA" if t["critical"] else "Normal"),tags=("critical",) if t["critical"] else ())
            self.show_explanation();self.draw_network()
            self.status.config(text=f"Análisis {self.mode.get()} correcto • {len(self.activities)} actividades")
        except ValueError as exc:
            self.status.config(text="Error: " + str(exc))
            messagebox.showerror("No se pudo calcular",str(exc))

    def show_explanation(self):
        r=self.result
        if not r:return
        lines=["CÁLCULO PASO A PASO", "="*65,
               f"Método: {r['mode']}","",
               "1) PASADA HACIA ADELANTE (inicios y finales tempranos)",
               "   ES = máximo EF de predecesoras (o 0 si no existen)",
               "   EF = ES + duración",""]
        for n in r["order"]:
            t=r["times"][n]
            lines.append(f"   {n:>5}: ES={fmt(t['ES']):>7}  EF={fmt(t['ES'])} + {fmt(t['d'])} = {fmt(t['EF'])}")
        lines.extend(["",f"   Duración total = máximo EF = {fmt(r['duration'])}","",
                      "2) PASADA HACIA ATRÁS (inicios y finales tardíos)",
                      "   LF = mínimo LS de sucesoras (o duración total si no existen)",
                      "   LS = LF - duración",""])
        for n in reversed(r["order"]):
            t=r["times"][n]
            lines.append(f"   {n:>5}: LF={fmt(t['LF']):>7}  LS={fmt(t['LF'])} - {fmt(t['d'])} = {fmt(t['LS'])}")
        lines.extend(["","3) HOLGURA = LS - ES = LF - EF","   Las actividades con holgura cero son críticas.",""])
        for n in r["order"]:
            t=r["times"][n]
            lines.append(f"   {n:>5}: {fmt(t['LS'])} - {fmt(t['ES'])} = {fmt(t['slack'])} {'  ← CRÍTICA' if t['critical'] else ''}")
        lines.extend(["","4) RUTAS CRÍTICAS",*("   " + " → ".join(p) for p in r["paths"])])
        if r["mode"]=="PERT":
            lines.extend(["","5) PERT: TIEMPO ESPERADO Y VARIANZA",
                          "   te = (a + 4m + b) / 6",
                          "   varianza = ((b - a) / 6)²",""])
            for n in r["order"]:
                a=r["by_name"][n];t=r["times"][n]
                lines.append(f"   {n}: te=({fmt(a.optimistic)}+4×{fmt(a.likely)}+{fmt(a.pessimistic)})/6={fmt(t['d'])}   var={t['v']:.4f}")
            lines.extend(["", "6) PROBABILIDAD APROXIMADA DE TERMINAR ANTES DE UNA FECHA",
                          "   En un proyecto con varias rutas críticas, la aproximación",
                          "   normal sobre una sola ruta puede subestimar el riesgo."])
            for i, v in enumerate(r["path_variances"],1):
                lines.append(f"   Ruta {i}: varianza={v:.4f}; desviación estándar={math.sqrt(v):.4f}")
            try:
                target=float(self.goal.get())
                if r["path_variances"]:
                    v=max(r["path_variances"])
                    if v>EPS:
                        z=(target-r["duration"])/math.sqrt(v)
                        probability=statistics.NormalDist().cdf(z)*100
                        lines.extend(["",f"   Meta de ejemplo: {fmt(target)} unidades",
                                      f"   Z=({fmt(target)} - {fmt(r['duration'])}) / {math.sqrt(v):.4f} = {z:.4f}",
                                      f"   Probabilidad estimada ≈ {probability:.2f}%",
                                      "   Supone aproximación normal y ruta crítica fija."])
                    else:
                        lines.append("   Varianza nula; no aplica aproximación normal.")
            except ValueError:pass
        self.explanation.config(state="normal");self.explanation.delete("1.0","end")
        self.explanation.insert("1.0","\n".join(lines));self.explanation.config(state="disabled")

    def draw_network(self):
        c=self.canvas;c.delete("all")
        r=self.result
        if not r:return
        width=max(c.winfo_width(),500);height=max(c.winfo_height(),200)
        by=r["by_name"];times=r["times"];successors=r["successors"]
        levels={}
        for n in r["order"]:
            levels[n]=1+max((levels[p] for p in by[n].predecessors),default=-1)
        columns=defaultdict(list)
        for n in r["order"]:columns[levels[n]].append(n)
        maxlevel=max(levels.values());marginx=54
        positions={}
        for level,names in columns.items():
            x=marginx+(width-2*marginx)*(level/(maxlevel or 1))
            for i,n in enumerate(names):
                y=(i+1)*height/(len(names)+1)
                positions[n]=(x,y)
        radius=20
        for n in r["order"]:
            for next_name in successors[n]:
                x1,y1=positions[n];x2,y2=positions[next_name]
                dx=x2-x1;dy=y2-y1;dist=math.hypot(dx,dy) or 1
                critical=times[n]["critical"] and times[next_name]["critical"] and abs(times[n]["EF"]-times[next_name]["ES"])<EPS
                c.create_line(x1+radius*dx/dist,y1+radius*dy/dist,x2-radius*dx/dist,y2-radius*dy/dist,
                              fill=RED if critical else BORDER,width=3 if critical else 2,arrow="last",arrowshape=(9,11,4))
        for n,(x,y) in positions.items():
            color=RED if times[n]["critical"] else BLUE
            c.create_oval(x-radius,y-radius,x+radius,y+radius,fill=color,outline="")
            c.create_text(x,y,text=n,fill=BG,font=("Segoe UI",11,"bold"))
            c.create_text(x,y+radius+12,text=f"t={fmt(times[n]['d'])}",fill=MUTED,font=("Segoe UI",9))
        c.create_text(15,12,anchor="nw",text="● Crítico     ● Normal",fill=MUTED,font=("Segoe UI",9))

    def save_json(self):
        path=filedialog.asksaveasfilename(defaultextension=".json",filetypes=[("JSON","*.json")])
        if not path:return
        data=[dict(name=a.name,predecessors=list(a.predecessors),optimistic=a.optimistic,likely=a.likely,pessimistic=a.pessimistic) for a in self.activities]
        Path(path).write_text(json.dumps(data,indent=2,ensure_ascii=False),encoding="utf-8")
        self.status.config(text="Proyecto guardado en JSON")

    def open_json(self):
        path=filedialog.askopenfilename(filetypes=[("JSON","*.json")])
        if not path:return
        try:
            raw=json.loads(Path(path).read_text(encoding="utf-8"))
            new=[Activity(str(a["name"]).upper(),tuple(str(p).upper() for p in a["predecessors"]),float(a["optimistic"]),float(a["likely"]),float(a["pessimistic"])) for a in raw]
            analyze(new,self.mode.get())
            self.activities=new;self.refresh();self.clear_fields();self.calculate()
        except (ValueError,KeyError,TypeError,OSError) as exc:messagebox.showerror("Archivo inválido",str(exc))

    def export_csv(self):
        if not self.result:return
        path=filedialog.asksaveasfilename(defaultextension=".csv",filetypes=[("CSV","*.csv")])
        if not path:return
        try:
            with open(path,"w",newline="",encoding="utf-8-sig") as f:
                w=csv.writer(f);w.writerow(["Actividad","Predecesoras","Duración","ES","EF","LS","LF","Holgura","Crítica","Varianza"])
                for n in self.result["order"]:
                    a=self.result["by_name"][n];t=self.result["times"][n]
                    w.writerow([n,", ".join(a.predecessors),t["d"],t["ES"],t["EF"],t["LS"],t["LF"],t["slack"],"Sí" if t["critical"] else "No",t["v"]])
            self.status.config(text="Resultados exportados a CSV")
        except OSError as exc:messagebox.showerror("Error al exportar",str(exc))

if __name__ == "__main__":
    Studio().mainloop()
