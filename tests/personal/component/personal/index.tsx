/* eslint-disable react-native/no-inline-styles */
/*
 *@Date: 2022-01-05 10:21:05
 *@Description: 个人中心固定区域入口
 */
import {
  CommonUtils,
  DeviceUtils,
  HttpService,
  screenSize as getScreenSize,
  WithTheme,
  Service as env,
  Http as httpservice,
  ScreenUtils,
  PlatformUtils,
  MCP_COUNTRY,
  MCP_LANG,
  RecordUtils,
} from '@hw-vmall/vrn-basic-comp';
import { ImageBackground as RNImageBackground } from '@hw-vmall/vrn-bussiness-comp';
import React, { Component } from 'react';
import { Platform, View } from 'react-native';
import ImgArray from '../../../../assets/ImgArray';
import { getUserCoupon, getUserVoucher } from '../../utils/util';
import UserInfo from './person-user-info/index';
// 个人资产
import PersonalAsster from './personal-asster/index';
import PersonalTitle from './personal-head';
import PersonalMyOrder from './personal-myorder/index';
import VMember from './vpro';
let iosStatusBarHeight: number = 0;
const TAG: string = 'PersonalHead';
if (PlatformUtils.isIOS()) {
  DeviceUtils.getStatusBarHeight()
    .then((result: any) => {
      iosStatusBarHeight = result;
    })
    .catch(() => {
      // do nothing
    });
}
export default class PersonalHead extends Component<any, any> {
  pageWidth: number;
  pageHeight: number;
  constructor(props) {
    super(props);
    this.state = {
      width: CommonUtils.getWindowSize('personal').screenWidth,
      height: CommonUtils.getWindowSize('personal').screenHeight,
      mergeStyle: null,
      dataPersonal: {
        integralt: '',
        coupon: '',
        voucher: '',
        symbol: this.isPc() ? '—' : '--',
      },
      unpaidOrderCount: '', // 未支付订单
      unreceiptOrderCount: '', // 待收货
      rmaAppCount: '', // 退换货
      count: '', // 评价
      isVpro: this.props.isVpro,
      latestOrderLogList: [], //订单进度列表
    };
  }
  getSize = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    return getScreenSize(this.pageWidth || width);
  };
  getHeight = () => {
    const height: number = CommonUtils.getWindowSize('personal').screenHeight;
    return getScreenSize(this.pageHeight || height);
  }
  isPc = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    return PlatformUtils.isPc(width);
  };
  isPad = () => {
    return this.getSize() === 'medium';
  };
  isApp = () => {
    return PlatformUtils.isApp();
  };
  isAndroid = () => {
    return PlatformUtils.isAndroid();
  };
  isWeb = () => {
    return PlatformUtils.isWeb();
  };
  async componentDidMount() {
    // WEB WAP 初始化获取登录状态
    if (this.props.isLogin) {
      // 个人资产
      this.getAssterInfo();
      // 我的订单
      this.getAssterInfoOrder();
      // 订单进度
      this.getScheduleInfoOrder();
    }
  }
  componentDidUpdate(prevProps: any) {
    if (
      this.state.width !== CommonUtils.getWindowSize('personal').screenWidth
    ) {
      this.setState({
        width: CommonUtils.getWindowSize('personal').screenWidth,
        height: CommonUtils.getWindowSize('personal').screenHeight,
      });
    }
    if (prevProps.isLogin !== this.props.isLogin && !this.props.isLogin) {
      this.setState({
        dataPersonal: {
          integralt: '',
          coupon: '',
          voucher: '',
          symbol: this.isPc() ? '—' : '--',
        },
        unpaidOrderCount: '', // 未支付订单
        unreceiptOrderCount: '', // 待收货
        rmaAppCount: '', // 退换货
        count: '', // 评价
        latestOrderLogList: [], //订单进度
      });
    }
    if (prevProps.isLogin !== this.props.isLogin && this.props.isLogin) {
      this.getAssterInfo();
      this.getAssterInfoOrder();
      this.getScheduleInfoOrder();
    }
  }

  handleAssterResult =(result: any[]) => {
    const integralt = result[0];
    let numIntegralt = '0';
    if (integralt?.pointBlance >= 0) {
      numIntegralt = integralt.pointBlance > 99999 ? '99999+' : integralt.pointBlance;
    }
    const coupon = result[1];
    let numCoupon = '0';
    if (coupon?.count >= 0) {
      numCoupon = coupon.count > 9999 ? '9999+' : coupon.count;
    }
    const voucher = result[2];
    let allVocher = '0.00';
    if (voucher?.bankBalanceAmount >= 0 && voucher.recyclerBalanceAmount >= 0) {
      allVocher = this.fixedNum(voucher.bankBalanceAmount + voucher.recyclerBalanceAmount);
    }
    const { dataPersonal } = this.state;
    this.setState({
      dataPersonal: {
        ...dataPersonal,
        integralt: numIntegralt,
        coupon: numCoupon,
        voucher: allVocher,
      },
    });
  }

  // 个人资产接口调用
  getAssterInfo = () => {
    // 用户积分
    const promiseInetral = HttpService.getUserIntegralt(CommonUtils.getPortal());
    const promiseCoupon = getUserCoupon();
    const promiseVoucher = getUserVoucher();
    Promise.all([promiseInetral, promiseCoupon, promiseVoucher]).then((result) => {
      this.handleAssterResult(result);
    });
  };

  // 查询各类型订单数量
  queryUserOrderCnt = () => {
    const commonParams = HttpService.getCommomParam();
    const url = `${env.openApiDomain}mcp/queryUserOrderCnt?${commonParams}&type=0&version=1`;
    return httpservice.get(url);
  };

  // 查询最近进度有变化的订单
  queryLatestOrderLogList = () => {
    const url = `${env.openApiDomain}mcp/order/queryLatestOrderLogList`;
    const portal: number = CommonUtils.getPortal();
    const parmas = {
      portal: String(portal),
      lang: MCP_LANG.CN,
      country: MCP_COUNTRY.CN,
    }
    return httpservice.post(url, parmas);
  };

  // 查询评价订单数量
  getNoCommentPrdCount = () => {
    const url = `${env.openApiDomain}rms/comment/getNoCommentPrdCount.json`;
    return httpservice.get(url);
  };

  // 查询评价订单数量-新接口
  getUnCommentPrdCount = () => {
    const url = `${env.openApiDomain}rms/v1/comment/getUnCommentPrdCount`;
    return httpservice.post(url);
  };

  handleGetNoCommentPrdCount = () => {
    this.getNoCommentPrdCount()
      .then((res: any) => {
        // 待评价
        this.setState({
          count: res.data.count,
        });
      })
      .catch((e) => {
        // do nothing
        RecordUtils.error(TAG, `getNoCommentPrdCount fail：${e?.stack}`);
      });
  };

  handleGetUnCommentPrdCount = () => {
    this.getUnCommentPrdCount()
      .then((res: any) => {
        // 待评价
        this.setState({
          count: res.data.count,
        });
      })
      .catch((e) => {
        // do nothing
        RecordUtils.error(TAG, `getUnCommentPrdCount fail：${e?.stack}`);
      });
  };

  // 订单进度
  getScheduleInfoOrder = () => {
    this.queryLatestOrderLogList()
      .then((res: any) => {
        // 待收货
        if (res.latestLogList?.length) {
          const latestOrderLogList = res.latestLogList.length > 10
           ? res.latestLogList.slice(0, 10)
           : res.latestLogList;
          this.setState({ latestOrderLogList });
        } else {
          this.setState({latestOrderLogList: []});
        }
      })
      .catch((e) => {
        this.setState({latestOrderLogList: []});
        RecordUtils.error(TAG, `queryLatestOrderLogList fail：${e?.stack}`);
      });
  };

  // 我的订单
  getAssterInfoOrder = () => {
    this.queryUserOrderCnt()
      .then((res) => {
        // 未支付订单

        if (res.unpaidOrderCount === undefined) {
          this.setState({
            unpaidOrderCount: 0,
          });
        } else {
          this.setState({
            unpaidOrderCount: res.unpaidOrderCount,
          });
        }
        // 待收货
        if (res.unreceiptOrderCount === undefined) {
          this.setState({
            unreceiptOrderCount: 0,
          });
        } else {
          this.setState({
            unreceiptOrderCount: res.unreceiptOrderCount,
          });
        }
        // 退换货
        if (res.rmaAppCount === undefined) {
          this.setState({
            rmaAppCount: 0,
          });
        } else {
          this.setState({
            rmaAppCount: res.rmaAppCount,
          });
        }
      })
      .catch((e) => {
        // do nothing
        RecordUtils.error(TAG, `queryUserOrderCnt fail：${e?.stack}`);
      });
    this.handleGetUnCommentPrdCount();
  };
  // 保留N位小数，默认两位
  fixedNum(val, n = 2) {
    if (val === 0) {
      return Number(val).toFixed(n);
    } else if (val > 9999) {
      return '9999+';
    } else {
      return parseFloat(val).toFixed(n);
    }
  }
  setmergeStyle = () => {
    const { personalStyleChange, pageType } = this.props;
    const styleChange = personalStyleChange;
    // 屏幕尺寸类型
    const size = getScreenSize(this.pageWidth || this.state.width);
    if (!CommonUtils.isEmpty(styleChange)) {
      return CommonUtils.getChangeStyle(styleChange, size, pageType);
    } else {
      return '';
    }
  };

  getScreen = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    const height: number = CommonUtils.getWindowSize('personal').screenHeight;
    return { width, height };
  };

  sourceResult = (newMergeStyle, isMember) => {
    if (this.isPc()) {
      return ImgArray.headeBgpc;
    }
  };

  getMyOrder = (isDisplayVPro, _width?: number, isPadH?: boolean) => {
    const {
      unpaidOrderCount, // 未支付订单
      unreceiptOrderCount,
      rmaAppCount,
      count,
      latestOrderLogList,
    } = this.state;
    const topOffset = isPadH ? 20 : 12;
    const top = isDisplayVPro ? topOffset : 0;
    return (
      <View
        style={[
          this.isPc()
            ? { position: 'relative', top: 12, left: -24 }
            : {
                position: 'relative',
                top,
                left: 0,
                paddingLeft: getScreenSize(_width) === 'medium' ? 24 : 16,
                paddingRight: getScreenSize(_width) === 'medium' ? 24 : 16,
                alignItems: 'center',
                marginTop: -2,
              },
          this.isApp() && {
            alignItems: 'center',
            marginTop: Platform.OS === 'ios' ? 8 : 0,
          },
          {
            zIndex: 0,
            width: '100%',
          },
        ]}
      >
        <PersonalMyOrder
          isLogin={this.props.isLogin}
          mpUid={this.props?.mpUid}
          unpaidOrderCount={unpaidOrderCount} // 未支付订单
          unreceiptOrderCount={unreceiptOrderCount}
          rmaAppCount={rmaAppCount}
          count={count}
          pageId={this.props?.pageId}
          width={_width}
          pageCatName={this.props.pageCatName}
          latestOrderLogList={latestOrderLogList}
        />
        <View
          style={{
            marginTop: PlatformUtils.isWap(_width) ? 0 : top,
            alignItems: 'center',
          }}
        />
      </View>
    );
  };

  render() {
    const { lang, isVpro, vproList } = this.props;
    const {
      dataPersonal,
    } = this.state;
    const disPlayApk =
      vproList?.configInfo && JSON.parse(vproList.configInfo)?.display;
    const mergeStyle = this.setmergeStyle();
    const disPlay = this.isApp() ? disPlayApk : vproList?.display;
    const isDisplayVPro =
      String(disPlay) === '1' &&
      String(this.props.enableAdvancedFeature) !== '0' &&
      !this.isPc();
    const isMember = isDisplayVPro && String(isVpro) === '1' && this.props.isLogin;
    return (
      <WithTheme>
        {(_styles, theme, _width, _height) => {
          this.pageWidth = _width;
          this.pageHeight = _height;
          let imgViewStyle = mergeStyle?.imgStyle?.backgroundColor ? mergeStyle.imgStyle : {};
          imgViewStyle = this.isPc() || isMember ? null : imgViewStyle;
          let padPadding = this.isPad() ? 24 : 16;
          padPadding = this.isPc() ? 100 : padPadding;
          const isPadH = ScreenUtils.isPadHorizontal(_width, _height);
          // 屏幕宽度-左侧导航栏-两边边距-中间间距
          const boxWidth = (_width - 32 - 16 - 16) / 2;
          const isWap = PlatformUtils.isWap(_width);
          return (
            <>
              <RNImageBackground
                resizeMode="stretch"
                style={[
                  {
                    position: 'relative',
                    zIndex: 1,
                  },
                ]}
                imgUri={isMember ? '' : mergeStyle?.bgImg}
                imgViewStyle={[imgViewStyle]}
                localSource={this.sourceResult(mergeStyle, isMember)}
                isFromPersonal={true}
              >
                <View
                  style={[
                    {
                      paddingHorizontal: padPadding,
                      zIndex: 11,
                    },
                    this.isPc() && { height: 200, paddingLeft: 100, paddingRight: 60, justifyContent: 'center' },
                  ]}
                >
                  {!(isWap || PlatformUtils.isHarmony()) && this.renderPersonalTitle(mergeStyle, isMember, _width)}
                  <View
                    style={[
                      isPadH && {
                        disPlay: 'flex',
                        flexDirection: 'row',
                        justifyContent: 'space-between',
                        alignItems: 'center',
                      },
                      isWap && { marginTop: 56 + 12 },
                    ]}
                  >
                    <UserInfo
                      enableAdvancedFeature={this.props.enableAdvancedFeature}
                      isLogin={this.props.isLogin}
                      isMember={isMember}
                      isDisplayVPro={isDisplayVPro}
                      avaImg={this.props.avaImg}
                      userName={this.props.userName}
                      userLevel={this.props.userLevel}
                      userAccount={this.props.userAccount}
                      mergeStyle={mergeStyle}
                      dataPersonal={dataPersonal}
                      pageId={this.props.pageId}
                      headStyle={this.props.headStyle}
                      width={_width}
                      boxWidth={boxWidth}
                      isPadH={isPadH}
                      vproList={vproList}
                    />
                    {!this.isPc() && (
                      <>
                        <View
                          style={{
                            marginTop: isPadH ? 0 : 12,
                          }}
                        >
                          <PersonalAsster
                            pageId={this.props.pageId}
                            lang={lang}
                            isLogin={this.props.isLogin}
                            personalData={dataPersonal}
                            isMember={isMember}
                            width={_width}
                            boxWidth={boxWidth}
                            isPadH={isPadH}
                            mergeStyle={mergeStyle}
                            pageCatName={this.props.pageCatName}
                          />
                        </View>
                      </>
                    )}
                  </View>
                </View>
                {isDisplayVPro ? (
                  <View
                    style={{
                      position: 'relative',
                      top: isPadH ? 16 : 12,
                      paddingHorizontal: this.isPad() ? 24 : 16,
                      borderRadius: 16,
                      overflow: 'hidden',
                    }}
                  >
                    <VMember
                      pageId={this.props.pageId}
                      vproList={vproList} // cms配置返回数据
                      isMember={isMember} // 是否开通
                    />
                  </View>
                ) : (
                  <>{!this.isPc() && this.getMyOrder(isDisplayVPro, _width, isPadH)}</>
                )}
              </RNImageBackground>
              {this.isPc() ? this.getMyOrder(isDisplayVPro, _width, isPadH) : isDisplayVPro && this.getMyOrder(isDisplayVPro, _width, isPadH)}
            </>
          );
        }}
      </WithTheme>
    );
  }

  private renderPersonalTitle(mergeStyle: any, isMember: any, _width: number) {
    const { vproList } = this.props;
    const {
      dataPersonal,
      unpaidOrderCount, // 未支付订单
      unreceiptOrderCount,
      rmaAppCount,
      count,
    } = this.state;
    if (this.isPc()) {
      return null;
    } else if (!PlatformUtils.isWeb()) {
      return (
        <PersonalTitle
          configInfo={this.props.configInfo}
          enableAdvancedFeature={this.props.enableAdvancedFeature}
          isShow={false}
          cartNum={this.props.cartNum}
          avaImg={this.props.avaImg}
          userName={this.props.userName}
          pageId={this.props.pageId}
          messageNum={this.props.messageNum}
          headStyle={this.props.headStyle}
          mergeStyle={mergeStyle}
          isLogin={this.props.isLogin}
          isMember={isMember}
          width={_width}
          vproList={vproList}
          statusBarHeight={this.props.statusBarHeight}
        />
      );
    } else {
      return (
        <PersonalTitle
          configInfo={this.props.configInfo}
          avaImg={this.props.avaImg}
          userName={this.props.userName}
          isLogin={this.props.isLogin}
          isShow={false}
          pageId={this.props.pageId}
          titleOpacity={this.props.titleOpacity}
          cartNum={this.props.cartNum}
          messageNum={this.props.messageNum}
          headStyle={this.props.headStyle}
          mergeStyle={mergeStyle}
          dataPersonal={dataPersonal}
          unpaidOrderCount={unpaidOrderCount} // 未支付订单
          unreceiptOrderCount={unreceiptOrderCount}
          rmaAppCount={rmaAppCount}
          count={count}
          isMember={isMember}
          width={_width}
          vproList={vproList}
        />
      );
    }
  }
}
