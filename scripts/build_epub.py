import os
import re
import zipfile
import markdown
from datetime import datetime, timezone

def generate_epub():
    base_dir = r"c:\Users\安卓人\Documents\antigravity\ai for math"
    md_path = r"C:\Users\安卓人\.gemini\antigravity\brain\be477108-f54b-49cc-bd95-a5dc71bd10c3\carmichael_architecture_handbook.md"
    output_epub_workspace = os.path.join(base_dir, "carmichael_architecture_handbook.epub")
    output_epub_artifact = r"C:\Users\安卓人\.gemini\antigravity\brain\be477108-f54b-49cc-bd95-a5dc71bd10c3\carmichael_architecture_handbook.epub"
    
    with open(md_path, "r", encoding="utf-8") as f:
        md_text = f.read()

    # Split markdown by top-level sections (## 1., ## 2., etc.)
    sections = re.split(r'\n(?=## \d+\. )', md_text)
    header_part = sections[0]
    chapters = sections[1:] if len(sections) > 1 else []

    # Read the full source codes for appendix
    smallest_path = os.path.join(base_dir, "Carmichael", "Smallest.lean")
    tactic_path = os.path.join(base_dir, "Carmichael", "Tactic.lean")
    
    with open(smallest_path, "r", encoding="utf-8") as f:
        smallest_code = f.read()
    with open(tactic_path, "r", encoding="utf-8") as f:
        tactic_code = f.read()

    # CSS styles
    css_content = """
@charset "utf-8";
body {
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", "PingFang SC", "Hiragino Sans GB", "Microsoft YaHei", "WenQuanYi Micro Hei", sans-serif;
    line-height: 1.7;
    color: #24292f;
    margin: 5% 7%;
    background-color: #ffffff;
}
h1, h2, h3, h4, h5, h6 {
    font-weight: 600;
    line-height: 1.35;
    color: #1f2328;
}
h1 {
    font-size: 1.85em;
    border-bottom: 2px solid #0969da;
    padding-bottom: 0.3em;
    margin-top: 1.2em;
    margin-bottom: 0.6em;
}
h2 {
    font-size: 1.45em;
    border-bottom: 1px solid #d0d7de;
    padding-bottom: 0.25em;
    margin-top: 1.3em;
    margin-bottom: 0.5em;
    color: #0969da;
}
h3 {
    font-size: 1.2em;
    margin-top: 1.1em;
    margin-bottom: 0.4em;
}
p {
    margin-top: 0.5em;
    margin-bottom: 0.8em;
    text-align: justify;
}
blockquote {
    border-left: 4px solid #0969da;
    background-color: #f6f8fa;
    padding: 0.6em 1em;
    margin: 0.8em 0;
    color: #57606a;
    border-radius: 0 4px 4px 0;
}
code {
    font-family: "Fira Code", Consolas, Monaco, "Courier New", monospace;
    font-size: 0.88em;
    background-color: #f0f2f5;
    padding: 0.2em 0.4em;
    border-radius: 4px;
    color: #cf222e;
}
pre {
    background-color: #f6f8fa;
    border: 1px solid #d0d7de;
    border-radius: 6px;
    padding: 12px 14px;
    overflow-x: auto;
    font-size: 0.85em;
    line-height: 1.45;
}
pre code {
    background-color: transparent;
    padding: 0;
    color: #24292f;
}
table {
    border-collapse: collapse;
    width: 100%;
    margin: 1em 0;
    font-size: 0.9em;
}
table, th, td {
    border: 1px solid #d0d7de;
}
th {
    background-color: #f6f8fa;
    font-weight: 600;
    padding: 8px 12px;
    text-align: left;
}
td {
    padding: 8px 12px;
}
tr:nth-child(even) {
    background-color: #fcfcfc;
}
.cover-container {
    text-align: center;
    padding: 4em 1em 2em 1em;
}
.cover-title {
    font-size: 2.1em;
    font-weight: bold;
    color: #0969da;
    margin-bottom: 0.3em;
    border-bottom: none;
}
.cover-subtitle {
    font-size: 1.15em;
    color: #57606a;
    margin-bottom: 2em;
    font-style: italic;
}
.cover-meta {
    font-size: 0.95em;
    color: #656d76;
    margin-top: 3em;
    line-height: 1.8;
}
.badge {
    display: inline-block;
    padding: 3px 8px;
    font-size: 0.8em;
    font-weight: 600;
    border-radius: 12px;
    background: #ddf4ff;
    color: #0969da;
    border: 1px solid #54aeff;
    margin: 2px;
}
"""

    def md_to_html(content):
        # Convert KaTeX / math blocks to readable formatting
        content = re.sub(r'\$\$(.*?)\$\$', r'<div style="text-align:center; margin:1em 0; font-family:serif; font-style:italic;">\1</div>', content, flags=re.DOTALL)
        content = re.sub(r'\$(.*?)\$', r'<span style="font-family:serif; font-style:italic;">\1</span>', content)
        html = markdown.markdown(content, extensions=['tables', 'fenced_code'])
        return html

    def wrap_xhtml(title, body_html):
        return f"""<?xml version="1.0" encoding="utf-8"?>
<!DOCTYPE html>
<html xmlns="http://www.w3.org/1999/xhtml" xmlns:epub="http://www.idpf.org/2007/ops" xml:lang="zh-CN">
<head>
    <meta charset="utf-8"/>
    <title>{title}</title>
    <link rel="stylesheet" type="text/css" href="style.css"/>
</head>
<body>
{body_html}
</body>
</html>"""

    # 1. Cover
    cover_html = """
    <div class="cover-container">
        <div class="cover-title">卡迈克尔数形式化工程<br/>新一代架构手册</div>
        <div class="cover-subtitle">V2.0 终极演进版 · 从破坏性 AST 到纯数论零魔数流水线</div>
        <div>
            <span class="badge">Lean 4.33.1</span>
            <span class="badge">Mathlib4 官方合规</span>
            <span class="badge">0 Magic Numbers</span>
            <span class="badge">现代 SMT grind 全迁移</span>
            <span class="badge">84 行极限高尔夫</span>
        </div>
        <div class="cover-meta">
            <p><strong>作　　者</strong>：Su MingKai (苏明凯)</p>
            <p><strong>项目代码</strong>：3y3y3y-huaiji/lean4-carmichael</p>
            <p><strong>生成日期</strong>：2026 年 9 月</p>
            <p><strong>授权许可</strong>：Apache License 2.0</p>
        </div>
    </div>
    """
    cover_xhtml = wrap_xhtml("封面", cover_html)

    # 2. Preface
    preface_body = md_to_html(header_part)
    preface_xhtml = wrap_xhtml("前言与架构定位", preface_body)

    # 3. Chapters
    chapter_data = []
    chapter_titles = [
        "第一章 全局架构演进总览",
        "第二章 零魔数双基底费马漏斗架构",
        "第三章 Korselt 自动化反射证明引擎",
        "第四章 现代 SMT 决策过程演进",
        "第五章 极限高尔夫源码精读与对照字典",
        "第六章 答辩答疑与 Mathlib 官方审查防御指南"
    ]

    for i, ch_text in enumerate(chapters):
        title = chapter_titles[i] if i < len(chapter_titles) else f"第 {i+1} 章"
        ch_body = md_to_html(ch_text)
        chapter_data.append((f"ch{i+1:02d}.xhtml", title, wrap_xhtml(title, ch_body)))

    # 4. Appendix: Pure Source Code
    appendix_text = f"""## 附录：全库形式化源码清单

### 附录 A: Carmichael/Smallest.lean (84 行极简极小性形式化)

```lean
{smallest_code}
```

### 附录 B: Carmichael/Tactic.lean (97 行 Korselt 自动化战术)

```lean
{tactic_code}
```
"""
    appendix_body = md_to_html(appendix_text)
    appendix_xhtml = wrap_xhtml("附录：源码清单", appendix_body)

    # Build EPUB package manifest & spine
    manifest_items = [
        ('style', 'style.css', 'text/css'),
        ('cover', 'cover.xhtml', 'application/xhtml+xml'),
        ('preface', 'preface.xhtml', 'application/xhtml+xml'),
    ]
    spine_items = ['cover', 'preface']

    for filename, title, _ in chapter_data:
        id_str = filename.replace('.xhtml', '')
        manifest_items.append((id_str, filename, 'application/xhtml+xml'))
        spine_items.append(id_str)

    manifest_items.append(('appendix', 'appendix.xhtml', 'application/xhtml+xml'))
    spine_items.append('appendix')

    manifest_items.append(('nav', 'nav.xhtml', 'application/xhtml+xml'))
    manifest_items.append(('ncx', 'toc.ncx', 'application/x-dtbncx+xml'))

    # OPF Content
    manifest_xml = "\n".join([f'    <item id="{item_id}" href="{href}" media-type="{media_type}"/>' + (' properties="nav"' if item_id == 'nav' else '') for item_id, href, media_type in manifest_items])
    spine_xml = "\n".join([f'    <itemref idref="{item_id}"/>' for item_id in spine_items])

    content_opf = f"""<?xml version="1.0" encoding="utf-8"?>
<package xmlns="http://www.idpf.org/2007/opf" unique-identifier="pub-id" version="3.0">
  <metadata xmlns:dc="http://purl.org/dc/elements/1.1/">
    <dc:identifier id="pub-id">urn:uuid:carmichael-architecture-handbook-v2</dc:identifier>
    <dc:title>卡迈克尔数形式化工程新一代架构手册（V2.0 终极演进版）</dc:title>
    <dc:creator>Su MingKai</dc:creator>
    <dc:language>zh-CN</dc:language>
    <dc:publisher>Formal Math &amp; Lean 4 Research Group</dc:publisher>
    <meta property="dcterms:modified">{datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')}</meta>
  </metadata>
  <manifest>
{manifest_xml}
  </manifest>
  <spine toc="ncx">
{spine_xml}
  </spine>
</package>
"""

    # Nav XHTML
    nav_links = [
        ('cover.xhtml', '封面'),
        ('preface.xhtml', '前言与阅读指南')
    ]
    for filename, title, _ in chapter_data:
        nav_links.append((filename, title))
    nav_links.append(('appendix.xhtml', '附录：源码清单'))

    nav_list_xml = "\n".join([f'      <li><a href="{href}">{title}</a></li>' for href, title in nav_links])
    nav_xhtml = f"""<?xml version="1.0" encoding="utf-8"?>
<!DOCTYPE html>
<html xmlns="http://www.w3.org/1999/xhtml" xmlns:epub="http://www.idpf.org/2007/ops" xml:lang="zh-CN">
<head>
    <meta charset="utf-8"/>
    <title>目录</title>
    <link rel="stylesheet" type="text/css" href="style.css"/>
</head>
<body>
  <nav epub:type="toc" id="toc">
    <h1>目录</h1>
    <ol>
{nav_list_xml}
    </ol>
  </nav>
</body>
</html>"""

    # NCX (EPUB 2 compatibility)
    nav_points = []
    for idx, (href, title) in enumerate(nav_links):
        nav_points.append(f"""    <navPoint id="navPoint-{idx+1}" playOrder="{idx+1}">
      <navLabel><text>{title}</text></navLabel>
      <content src="{href}"/>
    </navPoint>""")
    nav_points_xml = "\n".join(nav_points)

    toc_ncx = f"""<?xml version="1.0" encoding="utf-8"?>
<ncx xmlns="http://www.daisy.org/z3986/2005/ncx/" version="2005-1">
  <head>
    <meta name="dtb:uid" content="urn:uuid:carmichael-architecture-handbook-v2"/>
    <meta name="dtb:depth" content="1"/>
    <meta name="dtb:totalPageCount" content="0"/>
    <meta name="dtb:maxPageNumber" content="0"/>
  </head>
  <docTitle><text>卡迈克尔数形式化工程新一代架构手册（V2.0 终极演进版）</text></docTitle>
  <navMap>
{nav_points_xml}
  </navMap>
</ncx>
"""

    container_xml = """<?xml version="1.0" encoding="UTF-8"?>
<container version="1.0" xmlns="urn:oasis:names:tc:opendocument:xmlns:container">
  <rootfiles>
    <rootfile full-path="OEBPS/content.opf" media-type="application/oebps-package+xml"/>
  </rootfiles>
</container>"""

    # Create EPUB in both workspace and artifact dir
    for out_path in [output_epub_workspace, output_epub_artifact]:
        os.makedirs(os.path.dirname(out_path), exist_ok=True)
        with zipfile.ZipFile(out_path, 'w') as zf:
            # 1. mimetype (MUST be stored uncompressed, first file)
            zf.writestr('mimetype', 'application/epub+zip', compress_type=zipfile.ZIP_STORED)
            # 2. META-INF/container.xml
            zf.writestr('META-INF/container.xml', container_xml, compress_type=zipfile.ZIP_DEFLATED)
            # 3. OEBPS contents
            zf.writestr('OEBPS/style.css', css_content, compress_type=zipfile.ZIP_DEFLATED)
            zf.writestr('OEBPS/content.opf', content_opf, compress_type=zipfile.ZIP_DEFLATED)
            zf.writestr('OEBPS/nav.xhtml', nav_xhtml, compress_type=zipfile.ZIP_DEFLATED)
            zf.writestr('OEBPS/toc.ncx', toc_ncx, compress_type=zipfile.ZIP_DEFLATED)
            zf.writestr('OEBPS/cover.xhtml', cover_xhtml, compress_type=zipfile.ZIP_DEFLATED)
            zf.writestr('OEBPS/preface.xhtml', preface_xhtml, compress_type=zipfile.ZIP_DEFLATED)
            for filename, _, content in chapter_data:
                zf.writestr(f'OEBPS/{filename}', content, compress_type=zipfile.ZIP_DEFLATED)
            zf.writestr('OEBPS/appendix.xhtml', appendix_xhtml, compress_type=zipfile.ZIP_DEFLATED)
        print(f"Generated EPUB successfully at: {out_path} (Size: {os.path.getsize(out_path):,} bytes)")

if __name__ == '__main__':
    generate_epub()
