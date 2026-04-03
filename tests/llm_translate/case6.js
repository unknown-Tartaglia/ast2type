function groupByCategory(items) {
  if (!Array.isArray(items)) {
    return {};
  }

  const result = {};

  items.forEach(item => {
    if (item && typeof item === 'object' && item.category) {
      const category = item.category;
      if (!result[category]) {
        result[category] = [];
      }
      result[category].push({
        id: item.id,
        name: item.name,
        price: item.price
      });
    }
  });

  return result;
}

module.exports = groupByCategory;