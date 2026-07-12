import { DeviceUtils, HmiData, PlatformUtils ,E2EIdStore} from '@hw-vmall/vrn-basic-comp';

export default {
  // 点击个人资产
  hmiClickAsster(props: any, stage: string, contentName: string, spanId?: string) {
    if (!PlatformUtils.isAndroid()) {
      return;
    }
    const { pageId, pageCatName } = props;
    let basicData = HmiData.hmiBasicData(E2EIdStore.curPageType);
    const { e2eId, parentSpanId,} = basicData;
    const assterCategory = basicData?.category;
    const assterTagData= basicData?.tagData
    assterTagData?.push('个人信息');
    contentName && assterTagData?.push(contentName);
    return DeviceUtils.hmiLog({
      e2eId,
      parentSpanId,
      stage: stage,
      name: 'click',
      reportNow: 'true',
      spanId: spanId,
      content: {
        category: assterCategory,
        instanceId: pageId,
        instanceName: pageCatName,
        tag: assterTagData,
      },
    });
  },
};
