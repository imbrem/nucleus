---
name: work-on-docs-site
description: Maintain the Nucleus Svelte documentation application in apps/docs. Use for generated repository reports, dependency graph views, shared styling, page rendering, content/presentation separation, or docs-site tests and build failures.
---

# Work on the docs site

1. Read `apps/docs/package.json`, the route, and its data provider before editing.
2. Keep repository facts in typed data modules or generated inputs. Components
   render supplied content rather than embedding project status or vision.
3. Put graph layout, navigation, filtering, accessibility, and presentation
   policy behind shared components. Keep routes thin.
4. Preserve useful generated reports and remove stale copy only after locating
   its source. Do not present research notes as normative status.
5. Test transforms separately from rendering. Run the docs check, tests,
   production build, and formatting.
6. Inspect narrow and wide layouts, keyboard operation, focus, contrast, empty
   data, long names, and reduced-motion behavior after visual changes.
