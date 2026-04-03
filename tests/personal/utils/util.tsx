/*
 * @Date: 2021-12-20 16:06:01
 * @Description: 个人中心公共utils
 */
import {
  CommonUtils,
  Service as env,
  MCP_LANG,
  MCP_COUNTRY,
  Http as httpservice,
} from '@hw-vmall/vrn-basic-comp';

// 用户优惠券
export const getUserCoupon = (
  portal = CommonUtils.getPortal(),
  lang = MCP_LANG.CN,
  country = MCP_COUNTRY.CN,
  version = 1,
) => {
  const url = `${env.openApiDomain}mcp/queryUserCouponCnt?lang=${lang}&country=${country}&portal=${portal}&version=${version}`;
  return httpservice.get(url);
};
// 用户代金券
export const getUserVoucher = (
  portal = CommonUtils.getPortal(),
  lang = MCP_LANG.CN,
  country = MCP_COUNTRY.CN,
  version = 1,
) => {
  const url = `${env.openApiDomain}mcp/pay/queryTotalBalanceAmount`;
  const parmas: any = {};
  parmas.portal = parmas.portal || portal;
  parmas.lang = parmas.lang || MCP_LANG.CN;
  parmas.country = parmas.country || MCP_COUNTRY.CN;
  parmas.version = parmas.version || 1;
  return httpservice.post(url, parmas);
};
// N单
export const getCustomerVproInfo = () => {
  const url = `${env.openApiDomain}uc/getCustomerVproInfo`;
  return httpservice.post(url);
};
export const queryVproDiscountdetail = (parmas) => {
  const url = `${env.openApiDomain}uc/queryVproDiscountdetail`;
  return httpservice.post(url, parmas);
};
// 埋点indexName信息
export const handleIndexName = (index) => {
  let indexName;
  switch (index) {
    case 1:
      indexName = '头像';
      break;
    case 2:
      indexName = '昵称';
      break;
    case 3:
      indexName = '徽章';
      break;
    case 4:
      indexName = '我的等级';
      break;
    case 5:
      indexName = '收货地址';
      break;
    case 6:
      indexName = '每日签到';
      break;
    case 7:
      indexName = '积分';
      break;
    case 8:
      indexName = '优惠券';
      break;
    case 9:
      indexName = '代金券';
      break;
    case 10:
      indexName = '开通';
      break;
    case 11:
      indexName = 'N单返现';
      break;
    case 12:
      indexName = '会员店';
      break;
    default:
      break;
  }
  return indexName;
};
// 上报信息
export const contentAll = (actionCode, pageId, gotoURL, index) => {
  const data = {
    actionCode: actionCode?.toString(),
    actionName: '点击个人信息上报',
    pageId: pageId?.toString(),
    eventType: '2',
    content: {
      comId: 'personalInfo_head',
      gotoURL: gotoURL,
      index: index?.toString(),
      indexName: handleIndexName(index),
    },
    pageCatCode: 'p_personalCenter',
    pageCatName: '个人中心',
    resSiteCode: 's_personalCenter_head',
    resSiteName: '顶部卡片',
  };
  return { data };
};

export const getCardHeight = (card: any) => {
  const configInfo = card.props?.configInfo || {};
  const { disPlay } = configInfo;
  let height: number = 0;
  if (disPlay === '0') {
    height = 0;
  } else {
    height = 56;
  }
  return height;
};
