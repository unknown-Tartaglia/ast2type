function fetchRepoTree(
  ref?: string,
) {
    const branches = ref ? [ref] : ['HEAD', 'main', 'master'];
    return true;
}