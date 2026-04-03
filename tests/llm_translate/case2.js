function arrayIntersection(arr1, arr2) {
  if (!Array.isArray(arr1) || !Array.isArray(arr2)) {
    return [];
  }

  const set1 = new Set(arr1);
  const intersection = [];

  for (const item of arr2) {
    if (set1.has(item)) {
      intersection.push(item);
      set1.delete(item); // Remove to avoid duplicates in result
    }
  }

  return intersection;
}

module.exports = arrayIntersection;