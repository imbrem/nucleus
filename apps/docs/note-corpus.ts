// The `notes/` corpus, parsed from repository Markdown.
//
// Kept free of SvelteKit and filesystem imports on purpose: the site feeds it
// `import.meta.glob` results and the test feeds it files read from disk, so the
// rendered pages and the checks that gate them see exactly the same corpus.

import { Marked, type Tokens } from "marked";

export const NOTE_ROOT = "notes";

/// Status vocabulary from #569. A note that claims none of these is malformed
/// rather than merely undocumented: the point of the corpus is that a reader
/// can tell a research sketch from implemented behaviour at a glance.
export const NOTE_STATUSES = [
  "research",
  "proposal",
  "active",
  "superseded",
  "historical",
] as const;

export type NoteStatus = (typeof NOTE_STATUSES)[number];

export interface NoteMetadata {
  title: string;
  status: NoteStatus;
  /// Related issues and pull requests, as bare numbers or URLs.
  issues: string[];
  /// ISO date the note was last checked against the repository.
  reviewed?: string;
  /// Upstream revision for imported or researched external context.
  sourceRevision?: string;
  /// One-line description used in the navigation tree.
  summary?: string;
}

export interface Note {
  /// Repository-relative path, for example `notes/architecture/status.md`.
  path: string;
  /// Site slug beneath `/notes/`; empty for the corpus index.
  slug: string;
  metadata: NoteMetadata;
  body: string;
  headings: string[];
}

export interface CorpusProblem {
  path: string;
  message: string;
}

/// A link that leaves `notes/` but stays inside the repository. The site turns
/// these into source links; the test resolves them against the working tree.
export interface RepositoryLink {
  path: string;
  target: string;
}

export interface TreeEntry {
  slug: string;
  title: string;
  /// Absent when the path segment is only a directory, so navigation can show
  /// a grouping without linking to a page that was never written.
  status?: NoteStatus;
  summary?: string;
  children: TreeEntry[];
}

export interface Corpus {
  notes: Note[];
  bySlug: Map<string, Note>;
  tree: TreeEntry[];
  problems: CorpusProblem[];
  repositoryLinks: RepositoryLink[];
}

export interface RenderOptions {
  /// SvelteKit `base`, so links work under the Pages `BASE_PATH`.
  base: string;
  /// Revision used for links that leave the corpus; `main` when unknown.
  revision: string;
  /// Repository the source links point at.
  repository: string;
}

const FRONT_MATTER = /^---\r?\n([\s\S]*?)\r?\n---\r?\n?/;

function isStatus(value: string): value is NoteStatus {
  return (NOTE_STATUSES as readonly string[]).includes(value);
}

function scalar(value: string): string {
  const trimmed = value.trim();
  const quoted = /^"(.*)"$/.exec(trimmed) ?? /^'(.*)'$/.exec(trimmed);
  return quoted ? quoted[1] : trimmed;
}

/// Parse the small YAML subset the corpus convention actually uses: `key:
/// value` scalars plus flow (`[a, b]`) and block (`- a`) sequences.
///
/// A YAML dependency would buy nothing here. Front matter that needs more than
/// this is a sign the note is carrying structure that belongs in the body.
export function parseFrontMatter(source: string): {
  fields: Map<string, string[]>;
  body: string;
} | null {
  const matched = FRONT_MATTER.exec(source);
  if (!matched) return null;

  const fields = new Map<string, string[]>();
  let current: string[] | undefined;
  for (const line of matched[1].split(/\r?\n/)) {
    if (line.trim() === "" || line.trimStart().startsWith("#")) continue;
    const item = /^\s*-\s+(.*)$/.exec(line);
    if (item && current) {
      current.push(scalar(item[1]));
      continue;
    }
    const field = /^([A-Za-z][\w-]*)\s*:\s*(.*)$/.exec(line);
    if (!field) return null;
    const value = field[2].trim();
    const flow = /^\[(.*)\]$/.exec(value);
    current = flow
      ? flow[1]
          .split(",")
          .map(scalar)
          .filter((entry) => entry !== "")
      : value === ""
        ? []
        : [scalar(value)];
    fields.set(field[1], current);
  }
  return { fields, body: source.slice(matched[0].length) };
}

/// GitHub-compatible heading anchors, so `#some-heading` works the same way in
/// the rendered site as it does when reading the Markdown on GitHub.
export function headingId(text: string, seen: Map<string, number>): string {
  const base = text
    .toLowerCase()
    .replace(/`|\*|_|~/g, "")
    .replace(/\[([^\]]*)\]\([^)]*\)/g, "$1")
    .replace(/[^\p{Letter}\p{Number} -]/gu, "")
    .trim()
    .replace(/\s+/g, "-");
  const count = seen.get(base) ?? 0;
  seen.set(base, count + 1);
  return count === 0 ? base : `${base}-${count}`;
}

/// `notes/README.md` is the corpus index, and a directory `README.md` is that
/// directory's index, so both collapse onto their containing path.
export function noteSlug(path: string): string {
  const relative = path.slice(`${NOTE_ROOT}/`.length).replace(/\.md$/, "");
  return relative === "README"
    ? ""
    : relative.replace(/(^|\/)README$/, "").replace(/\/$/, "");
}

export function notePath(slug: string, base: string): string {
  return slug === "" ? `${base}/notes/` : `${base}/notes/${slug}/`;
}

function normalize(path: string): string | null {
  const segments: string[] = [];
  for (const segment of path.split("/")) {
    if (segment === "" || segment === ".") continue;
    if (segment !== "..") {
      segments.push(segment);
      continue;
    }
    if (segments.length === 0) return null;
    segments.pop();
  }
  return segments.join("/");
}

function headings(marked: Marked, body: string): string[] {
  const seen = new Map<string, number>();
  return marked
    .lexer(body)
    .filter((token): token is Tokens.Heading => token.type === "heading")
    .map((token) => headingId(token.text, seen));
}

function parseNote(
  path: string,
  source: string,
  problems: CorpusProblem[],
): Note | null {
  const parsed = parseFrontMatter(source);
  if (!parsed) {
    problems.push({
      path,
      message:
        "missing or malformed front matter; every note needs a `---` block with at least `title` and `status`",
    });
    return null;
  }

  const field = (name: string): string | undefined =>
    parsed.fields.get(name)?.[0];
  const title = field("title");
  const status = field("status");
  if (title === undefined || title === "") {
    problems.push({ path, message: "front matter is missing `title`" });
  }
  if (status === undefined || !isStatus(status)) {
    problems.push({
      path,
      message: `front matter \`status\` must be one of ${NOTE_STATUSES.join(", ")}, got ${status === undefined ? "nothing" : `\`${status}\``}`,
    });
  }
  const reviewed = field("reviewed");
  if (reviewed !== undefined && !/^\d{4}-\d{2}-\d{2}$/.test(reviewed)) {
    problems.push({
      path,
      message: `front matter \`reviewed\` must be an ISO date, got \`${reviewed}\``,
    });
  }
  if (title === undefined || status === undefined || !isStatus(status)) {
    return null;
  }

  const marked = new Marked({ gfm: true });
  return {
    path,
    slug: noteSlug(path),
    metadata: {
      title,
      status,
      issues: parsed.fields.get("issues") ?? [],
      reviewed,
      sourceRevision: field("source-revision"),
      summary: field("summary"),
    },
    body: parsed.body,
    headings: headings(marked, parsed.body),
  };
}

type LinkTarget =
  | { kind: "skip" }
  | { kind: "note"; note: Note; fragment: string }
  | { kind: "repository"; target: string; fragment: string }
  | { kind: "broken"; message: string };

/// Classify one Markdown link. Notes are written to be read on GitHub, so the
/// hrefs are ordinary repository-relative paths; this is what turns them into
/// site URLs and reports the ones that point at nothing.
export function resolveLink(
  corpus: Pick<Corpus, "bySlug">,
  note: Note,
  href: string,
): LinkTarget {
  if (href === "" || /^[a-z][a-z0-9+.-]*:/i.test(href) || href.startsWith("//"))
    return { kind: "skip" };

  const hash = href.indexOf("#");
  const target = hash === -1 ? href : href.slice(0, hash);
  const fragment = hash === -1 ? "" : href.slice(hash + 1);

  if (target === "") {
    return note.headings.includes(fragment)
      ? { kind: "note", note, fragment }
      : { kind: "broken", message: `no heading \`#${fragment}\` in this note` };
  }

  const directory = note.path.slice(0, note.path.lastIndexOf("/"));
  const resolved = href.startsWith("/")
    ? normalize(target)
    : normalize(`${directory}/${target}`);
  if (resolved === null) {
    return { kind: "broken", message: `\`${href}\` escapes the repository` };
  }
  if (resolved !== NOTE_ROOT && !resolved.startsWith(`${NOTE_ROOT}/`)) {
    return { kind: "repository", target: resolved, fragment };
  }

  // A link to a directory means that directory's index note.
  const slug = resolved.endsWith(".md")
    ? noteSlug(resolved)
    : resolved.slice(NOTE_ROOT.length).replace(/^\//, "");
  const found = corpus.bySlug.get(slug);
  if (!found) {
    return { kind: "broken", message: `\`${href}\` does not name a note` };
  }
  if (fragment !== "" && !found.headings.includes(fragment)) {
    return {
      kind: "broken",
      message: `\`${href}\` names \`${found.path}\`, which has no heading \`#${fragment}\``,
    };
  }
  return { kind: "note", note: found, fragment };
}

function collectLinks(note: Note, marked: Marked): string[] {
  const links: string[] = [];
  marked.use({
    walkTokens(token) {
      if (token.type === "link" || token.type === "image") {
        links.push((token as Tokens.Link).href);
      }
    },
  });
  marked.parse(note.body, { async: false });
  return links;
}

function insert(roots: TreeEntry[], note: Note): void {
  const segments = note.slug.split("/");
  let children = roots;
  for (const [index, segment] of segments.entries()) {
    const slug = segments.slice(0, index + 1).join("/");
    let entry = children.find((candidate) => candidate.slug === slug);
    if (!entry) {
      entry = { slug, title: segment, children: [] };
      children.push(entry);
    }
    if (index === segments.length - 1) {
      entry.title = note.metadata.title;
      entry.status = note.metadata.status;
      entry.summary = note.metadata.summary;
    }
    children = entry.children;
  }
}

/// Build the corpus from repository-relative Markdown paths.
///
/// The navigation tree comes from the paths themselves rather than a
/// hand-maintained index, so adding a note to a directory is the only step
/// needed to make it appear on the site.
export function buildCorpus(files: Record<string, string>): Corpus {
  const problems: CorpusProblem[] = [];
  const notes: Note[] = [];
  for (const path of Object.keys(files).sort()) {
    const note = parseNote(path, files[path], problems);
    if (note) notes.push(note);
  }

  const bySlug = new Map(notes.map((note) => [note.slug, note]));
  if (!bySlug.has("")) {
    problems.push({
      path: `${NOTE_ROOT}/README.md`,
      message: "the corpus index is missing",
    });
  }

  const repositoryLinks: RepositoryLink[] = [];
  const tree: TreeEntry[] = [];
  for (const note of notes) {
    if (note.slug !== "") insert(tree, note);
    for (const href of collectLinks(note, new Marked({ gfm: true }))) {
      const resolved = resolveLink({ bySlug }, note, href);
      if (resolved.kind === "broken") {
        problems.push({ path: note.path, message: resolved.message });
      } else if (resolved.kind === "repository") {
        repositoryLinks.push({ path: note.path, target: resolved.target });
      }
    }
  }

  return { notes, bySlug, tree, problems, repositoryLinks };
}

/// Render one note to HTML, rewriting repository-relative links so they work
/// from the deployed site without making the Markdown source unreadable on
/// GitHub.
export function renderNote(
  corpus: Corpus,
  note: Note,
  options: RenderOptions,
): string {
  const source = `https://github.com/${options.repository}/blob/${options.revision}`;
  const seen = new Map<string, number>();
  const marked = new Marked({ gfm: true });
  marked.use({
    walkTokens(token) {
      if (token.type !== "link" && token.type !== "image") return;
      const link = token as Tokens.Link;
      const resolved = resolveLink(corpus, note, link.href);
      if (resolved.kind === "note") {
        const suffix = resolved.fragment === "" ? "" : `#${resolved.fragment}`;
        link.href = `${notePath(resolved.note.slug, options.base)}${suffix}`;
      } else if (resolved.kind === "repository") {
        const suffix = resolved.fragment === "" ? "" : `#${resolved.fragment}`;
        link.href = `${source}/${resolved.target}${suffix}`;
      }
    },
    renderer: {
      heading(token) {
        const id = headingId(token.text, seen);
        const rendered = this.parser.parseInline(token.tokens);
        return `<h${token.depth} id="${id}">${rendered}</h${token.depth}>\n`;
      },
    },
  });
  return marked.parse(note.body, { async: false });
}

export function sourceUrl(note: Note, options: RenderOptions): string {
  return `https://github.com/${options.repository}/blob/${options.revision}/${note.path}`;
}
