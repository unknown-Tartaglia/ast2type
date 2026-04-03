import {
  DeviceUtils,
  HmiData,
  PlatformUtils,
  E2EIdStore,
} from '@hw-vmall/vrn-basic-comp';

const getIndexName = (item: any) => {
  const indexArray = {
    ic1: '退换/退款',
    ic2: '回收单',
    ic3: '待收货',
    ic4: '待评价',
    ic5: '待付款',
    all: '全部订单',
    ic_: '小程序',
  };
  return indexArray[item];
};

export default {
  // 点击我的订单
  hmiClickOrder(props: any, stage: string, item: string, spanId?: string) {
    if (!PlatformUtils.isAndroid()) {
      return;
    }
    const { pageId, pageCatName } = props;
    let basicData = HmiData.hmiBasicData(E2EIdStore.curPageType);
    const e2eId = basicData?.e2eId;
    const parentSpanId = basicData?.parentSpanId;
    const orderCategory = basicData?.category;
    const orderTagData = basicData?.tagData;
    orderTagData?.push('我的订单');
    const indexName = getIndexName(item);
    indexName && orderTagData?.push(indexName);
    return DeviceUtils.hmiLog({
      e2eId,
      parentSpanId,
      stage: stage,
      name: 'click',
      reportNow: 'true',
      spanId: spanId,
      content: {
        category: orderCategory,
        instanceId: pageId,
        instanceName: pageCatName,
        tag: orderTagData,
      },
    });
  },
};
