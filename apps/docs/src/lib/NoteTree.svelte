<script lang="ts">
  import { base } from "$app/paths";
  import { page } from "$app/state";
  import type { TreeEntry } from "../../note-corpus.ts";
  import NoteTree from "./NoteTree.svelte";

  let { entries }: { entries: TreeEntry[] } = $props();

  const current = $derived(page.url.pathname.replace(/\/$/, ""));
</script>

<ul class="note-tree">
  {#each entries as entry (entry.slug)}
    <li>
      {#if entry.status}
        <a
          href={`${base}/notes/${entry.slug}/`}
          aria-current={current === `${base}/notes/${entry.slug}`
            ? "page"
            : undefined}
        >
          {entry.title}
        </a>
        <span class={`status status-${entry.status}`}>{entry.status}</span>
      {:else}
        <span class="note-group">{entry.title}</span>
      {/if}
      {#if entry.children.length > 0}
        <NoteTree entries={entry.children} />
      {/if}
    </li>
  {/each}
</ul>
