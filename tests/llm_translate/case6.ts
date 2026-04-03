interface Item {
  id: number;
  name: string;
  price?: number;
  category: string;
}

interface ItemSummary {
  id: number;
  name: string;
  price?: number;
}

interface GroupedItems {
  [category: string]: ItemSummary[];
}

function groupByCategory(items: any[]): GroupedItems {
  if (!Array.isArray(items)) {
    return {};
  }

  const result: GroupedItems = {};

  items.forEach((item: any) => {
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