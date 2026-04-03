function arrayIntersection<T>(arr1: T[], arr2: T[]): T[] {
  if (!Array.isArray(arr1) || !Array.isArray(arr2)) {
    return [];
  }

  const set1 = new Set(arr1);
  const intersection: T[] = [];

  for (const item of arr2) {
    if (set1.has(item)) {
      intersection.push(item);
      set1.delete(item); // Remove to avoid duplicates in result
    }
  }

  return intersection;
}

module.exports = arrayIntersection;