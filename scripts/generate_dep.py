import re, sys, textwrap
from pathlib import Path
from typing import Iterable

PROJECT_ROOT = Path(__file__).resolve().parents[1]
THEORIES_ROOT = PROJECT_ROOT / "theories"
ROOT_MODULE_NAME = "Mcltt"
COLORS = {
    "Algorithmic": "darkturquoise",
    "Completeness": "deeppink3",
    "Core": "goldenrod",
    "Entrypoint": "steelblue1",
    "Syntactic": "darkorange",
    "Semantic": "forestgreen",
    "Soundness": "goldenrod1",
    "Frontend": "darkslategray4",
    "Extraction": "darkslategray3",
    "others": "lightpink",
}

GRAPH_SET: set[str] = set()
RANKED_GRAPH_SET: set[str] = set()

def under_subgraph(name: str, body: str) -> str:
    return f"""subgraph "{name}" {{ {body} }}"""

def subgraph_decl(*, name: str, label: str = "", tooltip: str = "", color: str, body: str = "") -> str:
    GRAPH_SET.add(name)
    return under_subgraph(name, f"""graph[color={color},fontcolor={color},label="{label}",tooltip="{tooltip}"]; node[fillcolor={color}]; {body}""")

def default_subgraph_decl(name: str, body: str = "") -> str:
    return subgraph_decl(name=name, label=name, tooltip=f"{ROOT_MODULE_NAME}.{name}", color=COLORS[name], body=body)

def core_subgraph_decl(name: str, body: str = "") -> str:
    return under_subgraph("Core", subgraph_decl(name=f"Core/{name}", label=name, tooltip=f"{ROOT_MODULE_NAME}.Core.{name}", color=COLORS[name], body=body))

DEPLINE_PATTERN = re.compile(r"(\S*\.vo).*:(.*)")
DEPSOURCE_PATTERN = re.compile(r"\S*\.vo")

def module_parts_of_path(path: str) -> tuple[str, ...]:
    return Path(path).resolve().relative_to(THEORIES_ROOT).with_suffix("").parts

def module_name_of_module_parts(parts: Iterable[str]) -> str:
    return f"""{ROOT_MODULE_NAME}.{".".join(parts)}"""

def module_name_of_path(path: str) -> str:
    return module_name_of_module_parts(module_parts_of_path(path))

def node_of_path(path: str) -> str:
    parts = module_parts_of_path(path)
    color = next((COLORS[parts[i]] for i in range(len(parts)-1,-1,-1) if parts[i] in COLORS),COLORS["others"])
    subgraph_names = ["/".join(parts[:partindex]) for partindex in range(1,len(parts))]
    module_name = module_name_of_module_parts(parts)
    node_label = parts[-1]

    # Handle special case for two main theorems
    # so that printed graph looks better
    if module_name == "Mcltt.Core.Completeness" or module_name == "Mcltt.Core.Soundness":
        result = under_subgraph(f"Core/{node_label}", f""""{module_name}"[label="{node_label}",tooltip="{module_name}",color={color},fillcolor=white];""")
    elif module_name == "Mcltt.LibTactics":
        result = f"""{{ graph[cluster=false,rank=min]; "{module_name}"[label="{node_label}",tooltip="{module_name}",fillcolor={color}]; }}"""
    else:
        result = f""""{module_name}"[label="{node_label}",tooltip="{module_name}",fillcolor={color}];"""

    for subgraph_name in reversed(subgraph_names):
        if subgraph_name in GRAPH_SET:
            if subgraph_name in RANKED_GRAPH_SET:
                result = under_subgraph(f"{subgraph_name}/rank", result)
            result = under_subgraph(subgraph_name, result)
        else:
            GRAPH_SET.add(subgraph_name)
            RANKED_GRAPH_SET.add(subgraph_name)
            result = under_subgraph(f"{subgraph_name}/rank", f"graph[cluster=false,rank=same]; {result}")
            result = under_subgraph(subgraph_name, f"""graph[cluster=true,label={parts[subgraph_names.index(subgraph_name)]},tooltip="{module_name_of_module_parts(subgraph_name.split("/"))}"]; {result}""")

    return result

def data_of_depline(depline: str) -> str:
    if result := DEPLINE_PATTERN.fullmatch(depline.strip()):
        sink_module = module_name_of_path(result.group(1))
        source_paths = result.group(2).split(" ")
        source_modules = (module_name_of_path(source_path) for source_path in source_paths if DEPSOURCE_PATTERN.match(source_path))
        edges = "\n".join(f""""{source_module}" -> "{sink_module}";""" for source_module in source_modules)
        return f"""{edges}{node_of_path(result.group(1))}"""
    else:
        raise ValueError(f"Broken Dependency: \"{depline}\"")

def gen_graph() -> str:
    newline = "\n"
    return textwrap.dedent(f"""
      digraph Mcltt {{
        graph [cluster=true,fontsize=28,label="Mcltt",labeljust=l,labelloc=t,penwidth=2,size=15,splines=true,tooltip=""];
        node [fontsize=18,shape=note,style=filled,URL="https://beluga-lang.github.io/McLTT/\\N.html"];
        {default_subgraph_decl("Algorithmic")}
        {default_subgraph_decl("Core")}
        {core_subgraph_decl("Completeness")}
        {core_subgraph_decl("Semantic")}
        {core_subgraph_decl("Soundness")}
        {core_subgraph_decl("Syntactic")}
        {default_subgraph_decl("Extraction")}
        {default_subgraph_decl("Frontend")}
        {textwrap.indent(newline.join(data_of_depline(depline) for depline in sys.stdin), "        ").lstrip()}
      }}""")

print(gen_graph())
