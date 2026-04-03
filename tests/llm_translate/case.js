function processProducts(products) {
  if (!Array.isArray(products)) {
    return [];
  }

  return products
    .filter(p => p && typeof p === 'object' && p.inStock === true)
    .map(p => {
      const finalPrice = p.discount ? p.price * (1 - p.discount / 100) : p.price;
      return {
        id: p.id,
        name: p.name,
        finalPrice: Math.round(finalPrice * 100) / 100,
        inStock: p.inStock
      };
    })
    .sort((a, b) => a.finalPrice - b.finalPrice);
}

module.exports = processProducts;