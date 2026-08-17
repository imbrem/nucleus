<script lang="ts">
  import { base } from "$app/paths";
  import NoteTree from "$lib/NoteTree.svelte";
  import type { LayoutProps } from "./$types";

  let { data, children }: LayoutProps = $props();
</script>

<main class="notes">
  <nav class="note-index" aria-label="Notes">
    <h3><a href={`${base}/notes/`}>Notes</a></h3>
    <NoteTree entries={data.tree} />
  </nav>
  {@render children()}
</main>
