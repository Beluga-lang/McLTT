from pathlib import Path
from xml.dom.minidom import parse
from xml.dom import Node
import io, sys

PROJECT_ROOT = Path(__file__).resolve().parents[1]

if 2 > len(sys.argv):
    print(f"{sys.argv[0]} requires an output file name", file = sys.stderr)
    exit(1)

SVG = parse(sys.stdin)
SVG_SCRIPT = parse((PROJECT_ROOT / "scripts" / "svg_script.html").open()).childNodes[0]
SVG_STYLE = parse((PROJECT_ROOT / "scripts" / "svg_style.html").open()).childNodes[0]
SVG_ELEMENT = SVG.getElementsByTagName("svg")[0]
SVG_ELEMENT.setAttribute("onload","addInteractivity(evt)")
SVG_ELEMENT.appendChild(SVG_STYLE)
SVG_ELEMENT.appendChild(SVG_SCRIPT)
OUTPUT_FILE = io.open(sys.argv[1], "w")
print(SVG.toprettyxml(), file = OUTPUT_FILE)
