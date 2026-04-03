interface Product {
  id: number;
  name: string;
  price: number;
  discount?: number | null;
  inStock: boolean;
}

interface ProcessedProduct {
  id: number;
  name: string;
  finalPrice: number;
  inStock: boolean;
}

function processProducts(products: any[]): ProcessedProduct[] {
  if (!Array.isArray(products)) {
    return [];
  }

  return products
    .filter((p: any): p is Product => p && typeof p === 'object' && p.inStock === true)
    .map((p: Product) => {
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